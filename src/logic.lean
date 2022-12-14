
section propositional

variables P Q R : Prop


------------------------------------------------
-- Proposições de dupla negaço:
------------------------------------------------

theorem doubleneg_intro :
  P → ¬¬P  :=
begin
  intros p not_p,
  contradiction,
end

theorem doubleneg_elim :
  ¬¬P → P  :=
begin
  intro double_not_p,
  by_cases not_p : P,
    apply not_p,
  have := double_not_p not_p,
  contradiction,
end

theorem doubleneg_law :
  ¬¬P ↔ P  :=
begin
  split,
  -- ⊢ ¬¬P → P
  have doubleneg_elim := doubleneg_elim,
  apply doubleneg_elim,
  -- ⊢ P → ¬¬P
  have doubleneg_intro := doubleneg_intro,
  apply doubleneg_intro,
end

------------------------------------------------
-- Comutatividade dos ∨,∧:
------------------------------------------------

theorem disj_comm :
  (P ∨ Q) → (Q ∨ P)  :=
begin
  intro p_or_q,
  cases p_or_q,
  right,
    apply p_or_q,
  left,
    apply p_or_q,
end

theorem conj_comm :
  (P ∧ Q) → (Q ∧ P)  :=
begin
  intro p_and_q,
  cases p_and_q,
  split,
  -- ⊢ Q
  apply p_and_q_right,
  -- ⊢ P
  apply p_and_q_left,
end

------------------------------------------------
-- Proposições de interdefinabilidade dos →,∨:
------------------------------------------------

theorem impl_as_disj_converse :
  (¬P ∨ Q) → (P → Q)  :=
begin
  intros not_p_or_q p,
  cases not_p_or_q,
  -- Case (-P)
  contradiction,
  -- Case (Q)
  apply not_p_or_q,
end

theorem disj_as_impl :
  (P ∨ Q) → (¬P → Q)  :=
begin
  intros p_or_q not_p,
  cases p_or_q,
  -- Case (P)
  contradiction,
  -- Case (Q),
  apply p_or_q,
end


------------------------------------------------
-- Proposições de contraposição:
------------------------------------------------

theorem impl_as_contrapositive :
  (P → Q) → (¬Q → ¬P)  :=
begin
  intros p_impl_q not_q p,
  have q : Q := p_impl_q p,
  contradiction,
end

theorem impl_as_contrapositive_converse :
  (¬Q → ¬P) → (P → Q)  :=
begin
  intros not_q_impl_not_p p,
  by_cases not_q : Q,
  apply not_q,
  have not_p : ¬P := not_q_impl_not_p not_q,
  contradiction,
end

theorem contrapositive_law :
  (P → Q) ↔ (¬Q → ¬P)  :=
begin
  split,
  -- ⊢ (P → Q) → ¬Q → ¬P
  have impl_as_contrapositive := impl_as_contrapositive,
  apply impl_as_contrapositive,
  -- ⊢ (¬Q → ¬P) → P → Q
  have impl_as_contrapositive_converse := impl_as_contrapositive_converse,
  apply impl_as_contrapositive_converse,
end


------------------------------------------------
-- A irrefutabilidade do LEM:
------------------------------------------------

theorem lem_irrefutable :
  ¬¬(P∨¬P)  :=
begin
  intro not_p_or_not_p,
  have p_or_not_p : P ∨ ¬P,
    right,
    intro p,
    have p_or_not_p' : P ∨ ¬P,
      left,
      apply p,
      contradiction,
    contradiction,
end


------------------------------------------------
-- A lei de Peirce
------------------------------------------------

theorem peirce_law_weak :
  ((P → Q) → P) → ¬¬P  :=
begin
  intros p_impl_q_impl_p not_p,
  have p_impl_q : (P → Q),
    intro p,
    contradiction,
  have p : P := p_impl_q_impl_p p_impl_q,
  contradiction,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∨,∧:
------------------------------------------------

theorem disj_as_negconj :
  P∨Q → ¬(¬P∧¬Q)  :=
begin
  intros p_or_q not_p_and_not_q,
  cases not_p_and_not_q,
  cases p_or_q,
  -- Case (P)
  contradiction,
  -- Case (Q)
  contradiction,
end

theorem conj_as_negdisj :
  P∧Q → ¬(¬P∨¬Q)  :=
begin
  intros p_or_q not_p_and_not_q,
  cases p_or_q,
  cases not_p_and_not_q,
  -- Case (¬P)
  contradiction,
  -- Case (¬Q)
  contradiction,
end


------------------------------------------------
-- As leis de De Morgan para ∨,∧:
------------------------------------------------

theorem demorgan_disj :
  ¬(P∨Q) → (¬P ∧ ¬Q)  :=
begin
  intro not_p_or_q,
  split,
  -- ⊢ ¬P
  intro p,
  have p_or_q : P∨Q,
    left,
    apply p,
  contradiction,
  -- ⊢ ¬Q
  intro q,
  have p_or_q : P∨Q,
    right,
    apply q,
  contradiction,
end

theorem demorgan_disj_converse :
  (¬P ∧ ¬Q) → ¬(P∨Q)  :=
begin
  intros not_p_and_not_q p_or_q,
  cases not_p_and_not_q,
  cases p_or_q,
  -- Case (P)
  contradiction,
  -- Case (Q)
  contradiction,
end

theorem demorgan_conj :
  ¬(P∧Q) → (¬Q ∨ ¬P)  :=
begin
  intro not_p_and_q,
  by_cases not_p : P,
  left,
  intro q,
  have p_and_q : P∧Q,
    split,
    -- ⊢ P
    apply not_p,
    -- ⊢ Q
    apply q,
    contradiction,
  right,
  contradiction,
end

theorem demorgan_conj_converse :
  (¬Q ∨ ¬P) → ¬(P∧Q)  :=
begin
  intros not_q_or_not_p p_and_q,
  cases p_and_q,
  cases not_q_or_not_p,
  -- Case (¬Q)
  contradiction,
  -- Case (¬P)
  contradiction,
end

theorem demorgan_conj_law :
  ¬(P∧Q) ↔ (¬Q ∨ ¬P)  :=
begin
  split,
  -- ⊢ ¬(P ∧ Q) → ¬Q ∨ ¬P
  have demorgan_conj := demorgan_conj,
  apply demorgan_conj,
  -- ⊢ ¬Q ∨ ¬P → ¬(P ∧ Q)
  have demorgan_conj_converse := demorgan_conj_converse,
  apply demorgan_conj_converse,
end

theorem demorgan_disj_law :
  ¬(P∨Q) ↔ (¬P ∧ ¬Q)  :=
begin
  split,
  -- ⊢ ¬(P ∨ Q) → ¬P ∧ ¬Q
  have demorgan_disj := demorgan_disj,
  apply demorgan_disj,
  -- ⊢ ¬P ∧ ¬Q → ¬(P ∨ Q)
  have demorgan_disj_converse := demorgan_disj_converse,
  apply demorgan_disj_converse,
end

------------------------------------------------
-- Proposições de distributividade dos ∨,∧:
------------------------------------------------

theorem distr_conj_disj :
  P∧(Q∨R) → (P∧Q)∨(P∧R)  :=
begin
    intro p_and_q_or_r,
    cases p_and_q_or_r,
    cases p_and_q_or_r_right,
    -- Case (Q)
        left,
        split,
        -- ⊢ P
        apply p_and_q_or_r_left,
        -- ⊢ Q
        apply p_and_q_or_r_right,
    -- Case (R)
        right,
        split,
        -- ⊢ P
        apply p_and_q_or_r_left,
        -- ⊢ R
        apply p_and_q_or_r_right,
end

theorem distr_conj_disj_converse :
  (P∧Q)∨(P∧R) → P∧(Q∨R)  :=
begin
  intro p_and_q_or_p_and_r,
  cases p_and_q_or_p_and_r,
  -- Case (P ∧ Q)
    cases p_and_q_or_p_and_r,
    split,
    apply p_and_q_or_p_and_r_left,
    left,
    apply p_and_q_or_p_and_r_right,
  -- Case (P ∧ R)
    cases p_and_q_or_p_and_r,
    split,
    apply p_and_q_or_p_and_r_left,
    right,
    apply p_and_q_or_p_and_r_right,
end

theorem distr_disj_conj :
  P∨(Q∧R) → (P∨Q)∧(P∨R)  :=
begin
  intro p_or_q_and_r,
  cases p_or_q_and_r,
  -- Case (P)
    split,
    -- ⊢ P ∨ Q
    left,
    apply p_or_q_and_r,
    -- ⊢ P ∨ R
    left,
    apply p_or_q_and_r,
  -- Case (Q ∧ R)
    cases p_or_q_and_r,
    split,
    -- ⊢ P ∨ Q
    right,
    apply p_or_q_and_r_left,
    -- ⊢ P ∨ R
    right,
    apply p_or_q_and_r_right,
end

theorem distr_disj_conj_converse :
  (P∨Q)∧(P∨R) → P∨(Q∧R)  :=
begin
  intro p_or_q_and_p_or_r,
  cases p_or_q_and_p_or_r,
  cases p_or_q_and_p_or_r_left,
  -- Case (P)
    left,
    apply p_or_q_and_p_or_r_left,
  -- Case (Q)
    cases p_or_q_and_p_or_r_right,
    -- Case (P)
      left,
      apply p_or_q_and_p_or_r_right,
    -- Case (R)
      right,
      split,
      -- ⊢ Q
      apply p_or_q_and_p_or_r_left,
      -- ⊢ R
      apply p_or_q_and_p_or_r_right,
end


------------------------------------------------
-- Currificação
------------------------------------------------

theorem curry_prop :
  ((P∧Q)→R) → (P→(Q→R))  :=
begin
  intros p_and_q_impl_r p q,
  have p_and_q : P∧Q,
    split,
    -- ⊢ P
    apply p,
    -- ⊢ Q
    apply q,
  have r : R := p_and_q_impl_r p_and_q,
  apply r,
end

theorem uncurry_prop :
  (P→(Q→R)) → ((P∧Q)→R)  :=
begin
  intros p_impl_q_impl_r p_and_q,
  cases p_and_q,
  have q_impl_r : Q→R :=  p_impl_q_impl_r p_and_q_left,
  have r : R := q_impl_r p_and_q_right,
  apply r,
end


------------------------------------------------
-- Reflexividade da →:
------------------------------------------------

theorem impl_refl :
  P → P  :=
begin
  intro p,
  apply p,
end

------------------------------------------------
-- Weakening and contraction:
------------------------------------------------

theorem weaken_disj_right :
  P → (P∨Q)  :=
begin
  intro p,
  left,
  apply p,
end

theorem weaken_disj_left :
  Q → (P∨Q)  :=
begin
  intro q,
  right,
  apply q,
end

theorem weaken_conj_right :
  (P∧Q) → P  :=
begin
  intro p_and_q,
  cases p_and_q,
  apply p_and_q_left,
end

theorem weaken_conj_left :
  (P∧Q) → Q  :=
begin
  intro p_and_q,
  cases p_and_q,
  apply p_and_q_right,
end

theorem conj_idempot :
  (P∧P) ↔ P :=
begin
  split,
  -- ⊢ P ∧ P → P
  intro p_and_p,
  cases p_and_p,
  apply p_and_p_left,
  -- ⊢ P → P ∧ P
  intro p,
  split,
  apply p,
  apply p,
end

theorem disj_idempot :
  (P∨P) ↔ P  :=
begin
  split,
  -- ⊢ P ∨ P → P
  intro p_or_p,
  cases p_or_p,
  apply p_or_p,
  apply p_or_p,
  -- ⊢ P → P ∨ P
  intro p,
  left,
  apply p,
end

end propositional


----------------------------------------------------------------


section predicate

variable U : Type
variables P Q : U -> Prop


------------------------------------------------
-- As leis de De Morgan para ∃,∀:
------------------------------------------------

theorem demorgan_exists :
  ¬(∃x, P x) → (∀x, ¬P x)  :=
begin
  intros not_exists_px x px,
  have contr_not_exists_px : (∃x, P x),
    existsi x,
    apply px,
  contradiction,
end

theorem demorgan_exists_converse :
  (∀x, ¬P x) → ¬(∃x, P x)  :=
begin
  intros forall_not_px exists_px,
  cases exists_px with x,
  have := forall_not_px x,
  contradiction,
end

theorem demorgan_forall :
  ¬(∀x, P x) → (∃x, ¬P x)  :=
begin
  intro not_forall_px,
  by_contradiction contr_not_forall_px,
  apply not_forall_px,
  intro forall_px,
  by_contradiction contr_forall_px,
  apply contr_not_forall_px,
  existsi forall_px,
  intro not_contr_forall_px,
  apply contr_forall_px not_contr_forall_px,
end

theorem demorgan_forall_converse :
  (∃x, ¬P x) → ¬(∀x, P x)  :=
begin
  intros exists_not_px forall_px,
  cases exists_not_px with x,
  have := forall_px x,
  contradiction,
end

theorem demorgan_forall_law :
  ¬(∀x, P x) ↔ (∃x, ¬P x)  :=
begin
  split,
  -- ⊢ (¬∀ (x : U), P x) → (∃ (x : U), ¬P x)
  have demorgan_forall := demorgan_forall,
  apply demorgan_forall,
  -- ⊢ (∃ (x : U), ¬P x) → (¬∀ (x : U), P x)
  have demorgan_forall_converse := demorgan_forall_converse,
  apply demorgan_forall_converse,
end

theorem demorgan_exists_law :
  ¬(∃x, P x) ↔ (∀x, ¬P x)  :=
begin
  split,
  -- ⊢ (¬∃ (x : U), P x) → ∀ (x : U), ¬P x
  have demorgan_exists := demorgan_exists,
  apply demorgan_exists,
  -- ⊢ (∀ (x : U), ¬P x) → (¬∃ (x : U), P x)
  have demorgan_exists_converse := demorgan_exists_converse,
  apply demorgan_exists_converse,
end


------------------------------------------------
-- Proposições de interdefinabilidade dos ∃,∀:
------------------------------------------------

theorem exists_as_neg_forall :
  (∃x, P x) → ¬(∀x, ¬P x)  :=
begin
  intros exists_px forall_not_px,
  cases exists_px with x,
  have := forall_not_px x,
  contradiction,
end

theorem forall_as_neg_exists :
  (∀x, P x) → ¬(∃x, ¬P x)  :=
begin
  intros forall_px exists_not_px,
  cases exists_not_px with x,
  have := forall_px x,
  contradiction,
end

theorem forall_as_neg_exists_converse :
  ¬(∃x, ¬P x) → (∀x, P x)  :=
begin
  intros not_exists_not_px x,
  by_contradiction contr_not_exists_not_px,
  have exists_not_px : (∃x, ¬P x),
    existsi x,
    apply contr_not_exists_not_px,
  contradiction,
end

theorem exists_as_neg_forall_converse :
  ¬(∀x, ¬P x) → (∃x, P x)  :=
begin
  intro not_forall_not_px,
  by_contradiction contr_not_forall_not_px,
  have forall_not_px : (∀x, ¬P x),
    intro x,
    intro px,
    have exists_px : (∃x, P x),
      existsi x,
      apply px,
    contradiction,
  contradiction,
end

theorem forall_as_neg_exists_law :
  (∀x, P x) ↔ ¬(∃x, ¬P x)  :=
begin
  split,
  -- ⊢ (∀ (x : U), P x) → (¬∃ (x : U), ¬P x)
  have forall_as_neg_exists := forall_as_neg_exists,
  apply forall_as_neg_exists,
  -- ⊢ (¬∃ (x : U), ¬P x) → ∀ (x : U), P x
  have forall_as_neg_exists_converse := forall_as_neg_exists_converse,
  apply forall_as_neg_exists_converse,
end

theorem exists_as_neg_forall_law :
  (∃x, P x) ↔ ¬(∀x, ¬P x)  :=
begin
  split,
  -- ⊢ (∃ (x : U), P x) → (¬∀ (x : U), ¬P x)
  have exists_as_neg_forall := exists_as_neg_forall,
  apply exists_as_neg_forall,
  -- ⊢ (¬∀ (x : U), ¬P x) → (∃ (x : U), P x)
  have exists_as_neg_forall_converse := exists_as_neg_forall_converse,
  apply exists_as_neg_forall_converse,
end

------------------------------------------------
--  Proposições de distributividade de quantificadores:
------------------------------------------------

theorem exists_conj_as_conj_exists :
  (∃x, P x ∧ Q x) → (∃x, P x) ∧ (∃x, Q x)  :=
begin
  intro exists_px_and_qx,
  cases exists_px_and_qx,
  split,
  -- ⊢ ∃ (x : U), P x
    existsi exists_px_and_qx_w,
    cases exists_px_and_qx_h,
      apply exists_px_and_qx_h_left,
  -- ⊢ ∃ (x : U), Q x
    existsi exists_px_and_qx_w,
    cases exists_px_and_qx_h,
      apply exists_px_and_qx_h_right,
end

theorem exists_disj_as_disj_exists :
  (∃x, P x ∨ Q x) → (∃x, P x) ∨ (∃x, Q x)  :=
begin
  intro exists_px_or_qx,
  cases exists_px_or_qx,
  cases exists_px_or_qx_h,
  -- Case (P exists_px_or_qx_w)
    left,
    existsi exists_px_or_qx_w,
    apply exists_px_or_qx_h,
  -- Case (Q exists_px_or_qx_w)
    right,
    existsi exists_px_or_qx_w,
    apply exists_px_or_qx_h,
  
end

theorem exists_disj_as_disj_exists_converse :
  (∃x, P x) ∨ (∃x, Q x) → (∃x, P x ∨ Q x)  :=
begin
  intro exists_px_or_exists_qx,
  cases exists_px_or_exists_qx,
  -- Case (∃ (x : U), P x)
    cases exists_px_or_exists_qx,
      existsi exists_px_or_exists_qx_w,
      left,
      apply exists_px_or_exists_qx_h,
  -- Case (∃ (x : U), Q x)
    cases exists_px_or_exists_qx,
      existsi exists_px_or_exists_qx_w,
      right,
      apply exists_px_or_exists_qx_h,
end

theorem forall_conj_as_conj_forall :
  (∀x, P x ∧ Q x) → (∀x, P x) ∧ (∀x, Q x)  :=
begin
  intro forall_px_and_qx,
  split,
  -- ⊢ ∀ (x : U), P x
  intro x,
  have px_and_qx : (P x ∧ Q x) := forall_px_and_qx x,
    cases px_and_qx,
      apply px_and_qx_left,
  -- ⊢ ∀ (x : U), Q x
  intro x,
  have px_and_qx : (P x ∧ Q x) := forall_px_and_qx x,
    cases px_and_qx,
      apply px_and_qx_right,
end

theorem forall_conj_as_conj_forall_converse :
  (∀x, P x) ∧ (∀x, Q x) → (∀x, P x ∧ Q x)  :=
begin
  intro forall_px_and_forall_qx,
  cases forall_px_and_forall_qx,
  intro forall_px_and_qx,
  split,
  -- ⊢ P forall_px_and_qx
  apply forall_px_and_forall_qx_left,
  -- ⊢ Q forall_px_and_qx
  apply forall_px_and_forall_qx_right,
end

theorem forall_disj_as_disj_forall_converse :
  (∀x, P x) ∨ (∀x, Q x) → (∀x, P x ∨ Q x)  :=
begin
  intros forall_px_or_forall_qx forall_px_or_qx,
  cases forall_px_or_forall_qx,
  -- Case (∀ (x : U), P x)
    left,
    apply forall_px_or_forall_qx,
  -- Case (∀ (x : U), Q x)
    right,
    apply forall_px_or_forall_qx,
end

/- NOT THEOREMS --------------------------------

theorem forall_disj_as_disj_forall :
  (∀x, P x ∨ Q x) → (∀x, P x) ∨ (∀x, Q x)  :=
begin
end

theorem exists_conj_as_conj_exists_converse :
  (∃x, P x) ∧ (∃x, Q x) → (∃x, P x ∧ Q x)  :=
begin
end

---------------------------------------------- -/

end predicate
