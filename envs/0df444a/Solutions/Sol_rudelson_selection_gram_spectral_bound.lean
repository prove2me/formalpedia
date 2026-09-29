-- Prove2me | solution 1 for rudelson_selection_gram_spectral_bound
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T17:17:09.492714+00:00
-- url     : https://prove2.me/submissions/e48dfe9c-61bc-4a4e-a75d-4467e4112975

import Theorems.Thm_spectral_norm_loewner_monotone
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Data.Real.StarOrdered

open scoped Matrix RealInnerProductSpace BigOperators
open RCLike ContinuousLinearMap

theorem solution {d : ℕ} {ι : Type*}
    (s : Finset ι) (y : ι → Fin d → ℝ) (M : ℝ) (hM0 : 0 ≤ M)
    (hM : ∀ c ∈ s, (y c ⬝ᵥ y c) ≤ M) :
    ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c))‖
      ≤ M * ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
        (∑ c ∈ s, Matrix.vecMulVec (y c) (y c))‖ := by
  -- nonneg-scalar PSD helper.
  have posSemidef_smul : ∀ {M' : Matrix (Fin d) (Fin d) ℝ}, M'.PosSemidef →
      ∀ {c : ℝ}, 0 ≤ c → (c • M').PosSemidef := by
    intro M' hM' c hc
    refine ⟨hM'.1.smul (IsSelfAdjoint.all c), fun x => ?_⟩
    have hsum : (x.sum fun i xi => x.sum fun j xj => star xi * (c • M') i j * xj)
        = c * (x.sum fun i xi => x.sum fun j xj => star xi * M' i j * xj) := by
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr (fun i _ => ?_)
      rw [Finsupp.mul_sum]
      refine Finsupp.sum_congr (fun j _ => ?_)
      simp only [Matrix.smul_apply, smul_eq_mul]; ring
    rw [hsum]; exact mul_nonneg hc (hM'.2 x)
  set A := ∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c) with hA
  set B := M • (∑ c ∈ s, Matrix.vecMulVec (y c) (y c)) with hB
  -- A is PSD.
  have hApsd : A.PosSemidef := by
    rw [hA]
    refine Matrix.posSemidef_sum s (fun c hc => ?_)
    refine posSemidef_smul ?_ ?_
    · have hstar : Matrix.vecMulVec (y c) (y c) = Matrix.vecMulVec (y c) (star (y c)) := by
        simp [star]
      rw [hstar]; exact Matrix.posSemidef_vecMulVec_self_star (y c)
    · have hself : y c ⬝ᵥ y c = ∑ i, y c i * y c i := rfl
      rw [hself]
      exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  -- B - A is PSD.
  have hBA : (B - A).PosSemidef := by
    have hkey : B - A
        = ∑ c ∈ s, (M - (y c ⬝ᵥ y c)) • Matrix.vecMulVec (y c) (y c) := by
      rw [hB, hA, Finset.smul_sum, ← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl (fun c _ => ?_)
      rw [sub_smul]
    rw [hkey]
    refine Matrix.posSemidef_sum s (fun c hc => ?_)
    refine posSemidef_smul ?_ (by linarith [hM c hc])
    have hstar : Matrix.vecMulVec (y c) (y c) = Matrix.vecMulVec (y c) (star (y c)) := by
      simp [star]
    rw [hstar]; exact Matrix.posSemidef_vecMulVec_self_star (y c)
  -- Apply the imported Loewner→spectral monotonicity.
  have hmono := spectral_norm_loewner_monotone A B hApsd hBA
  -- Unfold the scalar in ‖toEuclideanCLM B‖.
  have hsmul : ‖Matrix.toEuclideanCLM (𝕜 := ℝ) B‖
      = M * ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (∑ c ∈ s, Matrix.vecMulVec (y c) (y c))‖ := by
    rw [hB]
    rw [show Matrix.toEuclideanCLM (𝕜 := ℝ) (M • (∑ c ∈ s, Matrix.vecMulVec (y c) (y c)))
          = M • Matrix.toEuclideanCLM (𝕜 := ℝ) (∑ c ∈ s, Matrix.vecMulVec (y c) (y c)) from
        map_smul _ _ _, norm_smul]
    simp [Real.norm_eq_abs, abs_of_nonneg hM0]
  rw [hsmul] at hmono
  exact hmono

#print axioms solution
