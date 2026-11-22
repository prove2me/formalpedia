-- Prove2me | solution 1 for rademacherCorrelation_abs_le_one
-- status  : ACCEPTED   (prove)
-- author  : @marwahaha
-- created : 2026-11-22T05:38:39.62479+00:00
-- url     : https://prove2.me/submissions/300a1503-7fe6-4464-bf8c-01c736a2c049

module
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Generalization_Core
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series
public import Mathlib.MeasureTheory.Integral.Bochner.Set
public import Definitions.Def_LeanPool_FormalLearningTheory_Complexity_Rademacher
public import Theorems.Thm_boolToSign_mul_abs_le_one

set_option autoImplicit true
@[expose] public section
public section
universe u v
theorem _root_.solution {X : Type u} {m : ℕ} (hm : 0 < m)
    (h : Concept X Bool) (σ : SignVector m) (xs : Fin m → X) :
    |rademacherCorrelation h σ xs| ≤ 1 := by
  unfold rademacherCorrelation
  rw [dif_neg (by omega)]
  have hm_pos : (0 : ℝ) < m := Nat.cast_pos.mpr hm
  rw [abs_mul, abs_div, abs_one, abs_of_pos hm_pos]
  have hsum_le : |∑ i : Fin m, boolToSign (σ i) * boolToSign (h (xs i))| ≤ m := by
    let f := fun i : Fin m => boolToSign (σ i) * boolToSign (h (xs i))
    change |∑ i, f i| ≤ ↑m
    have h1 : |∑ i, f i| ≤ ∑ i, ‖f i‖ := norm_sum_le Finset.univ f
    have h2 : ∀ i : Fin m, ‖f i‖ ≤ 1 := by
      intro i; rw [Real.norm_eq_abs]; exact boolToSign_mul_abs_le_one (σ i) (h (xs i))
    have h3 : ∑ i : Fin m, ‖f i‖ ≤ ∑ _i : Fin m, (1 : ℝ) :=
      Finset.sum_le_sum (fun i _ => h2 i)
    have h4 : ∑ _i : Fin m, (1 : ℝ) = m := by simp [Finset.sum_const]
    linarith
  calc 1 / (m : ℝ) * |∑ i, boolToSign (σ i) * boolToSign (h (xs i))|
      ≤ 1 / m * m := by
        simp_all
    _ = 1 := by field_simp
