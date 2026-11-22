-- Prove2me | solution 1 for covering_minimax
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:33:06.62339+00:00
-- url     : https://prove2.me/submissions/3cefc27a-9fdf-4dff-bd59-76ee498cd686

module
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_KLDivergence
public import Mathlib.Algebra.BigOperators.Field
public import Definitions.Def_LeanPool_FormalLearningTheory_PureMath_ApproxMinimax
public import Theorems.Thm_exists_covering_row

set_option autoImplicit true
@[expose] public section
public section
open Finset
noncomputable section
theorem _root_.solution
    {R C : Type*} [Fintype R] [Fintype C] [Nonempty C]
    (M : R → C → Bool) (v : ℝ) (hv : 0 < v)
    (hrow : ∀ q : FinitePMF C, ∃ r : R,
      v ≤ ∑ c, q.prob c * (if M r c then (1 : ℝ) else 0)) :
    ∃ p : FinitePMF R, ∀ c : C,
      (1 : ℝ) / Fintype.card C ≤ boolGamePayoff M p c := by
  classical
  have hcover := exists_covering_row M v hv hrow
  choose r_c hr_c using hcover
  let n := Fintype.card C
  have hn : 0 < n := Fintype.card_pos
  let eC := (Fintype.equivFin C).symm
  let rs : Fin n → R := fun i => r_c (eC i)
  refine ⟨empiricalPMF hn rs, fun c₀ => ?_⟩
  simp only [boolGamePayoff]
  let i₀ : Fin n := (Fintype.equivFin C) c₀
  have hrs_i₀ : rs i₀ = r_c c₀ := by
    simp only [rs, eC, i₀, Equiv.symm_apply_apply]
  calc (1 : ℝ) / n
      = (1 : ℝ) / n * 1 := (mul_one _).symm
    _ ≤ (empiricalPMF hn rs).prob (r_c c₀) * (if M (r_c c₀) c₀ then 1 else 0) := by
        simp only [hr_c c₀]
        apply mul_le_mul_of_nonneg_right _ (by norm_num)
        simp only [empiricalPMF]
        apply div_le_div_of_nonneg_right _ (Nat.cast_nonneg _)
        rw [Nat.one_le_cast]
        apply Finset.card_pos.mpr
        exact ⟨i₀, by simp [hrs_i₀]⟩
    _ ≤ ∑ r : R, (empiricalPMF hn rs).prob r * (if M r c₀ then 1 else 0) := by
        apply Finset.single_le_sum (f := fun r =>
          (empiricalPMF hn rs).prob r * (if M r c₀ then (1 : ℝ) else 0))
        · intro r _
          exact mul_nonneg ((empiricalPMF hn rs).prob_nonneg r) (by split_ifs <;> norm_num)
        · exact mem_univ _
