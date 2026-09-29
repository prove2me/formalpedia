-- Prove2me | solution 1 for sum_norm_sq_rank_one_outer_product_loewner_le_scalar_mul_sum
-- status  : ACCEPTED   (prove)
-- author  : @LukeBernese
-- created : 2026-06-24T01:32:32.046181+00:00
-- url     : https://prove2.me/submissions/a86fff1c-6565-4113-9ee3-c28b99afb016

import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.StarOrdered

open scoped BigOperators Matrix

namespace LoewnerHelper

/-- A nonnegative real scalar multiple of a PSD matrix is PSD. -/
theorem posSemidef_smul {d : ℕ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : M.PosSemidef)
    {c : ℝ} (hc : 0 ≤ c) : (c • M).PosSemidef := by
  refine ⟨hM.1.smul (IsSelfAdjoint.all c), fun x => ?_⟩
  have hsum : (x.sum fun i xi => x.sum fun j xj => star xi * (c • M) i j * xj)
      = c * (x.sum fun i xi => x.sum fun j xj => star xi * M i j * xj) := by
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun i _ => ?_)
    rw [Finsupp.mul_sum]
    refine Finsupp.sum_congr (fun j _ => ?_)
    simp only [Matrix.smul_apply, smul_eq_mul]
    ring
  rw [hsum]
  exact mul_nonneg hc (hM.2 x)

end LoewnerHelper

theorem solution {d : ℕ} {ι : Type*} (s : Finset ι) (y : ι → Fin d → ℝ) (M : ℝ)
    (hM : ∀ c ∈ s, (y c ⬝ᵥ y c) ≤ M) :
    (M • (∑ c ∈ s, Matrix.vecMulVec (y c) (y c))
        - ∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c)).PosSemidef := by
  have hkey : M • (∑ c ∈ s, Matrix.vecMulVec (y c) (y c))
      - ∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c)
      = ∑ c ∈ s, (M - (y c ⬝ᵥ y c)) • Matrix.vecMulVec (y c) (y c) := by
    rw [Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl (fun c _ => ?_)
    rw [sub_smul]
  rw [hkey]
  refine Matrix.posSemidef_sum s (fun c hc => ?_)
  refine LoewnerHelper.posSemidef_smul ?_ (by linarith [hM c hc])
  have hstar : Matrix.vecMulVec (y c) (y c) = Matrix.vecMulVec (y c) (star (y c)) := by
    simp [star]
  rw [hstar]
  exact Matrix.posSemidef_vecMulVec_self_star (y c)
