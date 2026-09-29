-- Prove2me | solution 1 for rank_one_variance_proxy_eigenvalue_le_radius_sq_gram_opnorm
-- status  : ACCEPTED   (prove)
-- author  : @Minghui
-- created : 2026-06-25T22:34:55.772557+00:00
-- url     : https://prove2.me/submissions/c2dd5fbf-686a-480e-9b3f-0b4ee35dbf12

import Theorems.Thm_sum_rank_one_outer_product_square_collapse
import Theorems.Thm_rudelson_selection_gram_spectral_bound
import Mathlib.Analysis.Matrix.PosDef
import Mathlib.Analysis.Matrix.Order
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Real.Basic

open Matrix
open scoped BigOperators Matrix Matrix.Norms.L2Operator MatrixOrder

set_option maxHeartbeats 1000000

private lemma opNorm_toContinuousLinearMap_toEuclideanLin {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) :
    ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))‖ = ‖A‖ :=
  (Matrix.l2_opNorm_def A).symm

private theorem hermitian_eigenvalue_le_toEuclideanLin_opnorm {d : Nat}
    (A : Matrix (Fin d) (Fin d) ℝ) (hA : A.IsHermitian) (i : Fin d) :
    hA.eigenvalues i ≤
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))‖ := by
  let v : EuclideanSpace ℝ (Fin d) := hA.eigenvectorBasis i
  let T := LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A)
  have hvnorm : ‖v‖ = 1 := by
    dsimp [v]
    exact hA.eigenvectorBasis.norm_eq_one i
  have hTv : T v = (hA.eigenvalues i) • v := by
    apply WithLp.ofLp_injective 2
    simpa [T, v] using hA.mulVec_eigenvectorBasis i
  have hbound : ‖T v‖ ≤ ‖T‖ * ‖v‖ := T.le_opNorm v
  have hbound_abs : |hA.eigenvalues i| ≤ ‖T‖ := by
    simpa [hTv, norm_smul, hvnorm, Real.norm_eq_abs] using hbound
  exact (le_abs_self (hA.eigenvalues i)).trans (by simpa [T] using hbound_abs)

theorem solution
    {d : Nat} {ι : Type*} [Fintype ι] [DecidableEq ι]
    (s : Finset ι) (y : ι → Fin d → ℝ) (R : ℝ)
    (hR_nonneg : 0 ≤ R)
    (hRadius : ∀ c ∈ s, (y c ⬝ᵥ y c) ≤ R ^ 2) :
    let G : Matrix (Fin d) (Fin d) ℝ :=
      ∑ c ∈ s, Matrix.vecMulVec (y c) (y c)
    let V : Matrix (Fin d) (Fin d) ℝ :=
      ∑ c ∈ s, Matrix.vecMulVec (y c) (y c) * Matrix.vecMulVec (y c) (y c)
    (hGHerm : G.IsHermitian) →
    (hVHerm : V.IsHermitian) →
    ∀ i : Fin d,
      hVHerm.eigenvalues i ≤
        R ^ 2 * ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G))‖ := by
  intro G V hGHerm hVHerm i
  have hR2_nonneg : 0 ≤ R ^ 2 := pow_nonneg hR_nonneg 2
  have hRewrite :
      V = ∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c) := by
    simpa [V] using sum_rank_one_outer_product_square_collapse (d := d) s y
  have hEig :
      hVHerm.eigenvalues i ≤
        ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin V))‖ :=
    hermitian_eigenvalue_le_toEuclideanLin_opnorm V hVHerm i
  have hNorm :
      ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
          (∑ c ∈ s, (y c ⬝ᵥ y c) • Matrix.vecMulVec (y c) (y c))‖
        ≤ R ^ 2 *
          ‖Matrix.toEuclideanCLM (𝕜 := ℝ)
            (∑ c ∈ s, Matrix.vecMulVec (y c) (y c))‖ :=
    rudelson_selection_gram_spectral_bound s y (R ^ 2) hR2_nonneg hRadius
  have hNorm' :
      ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin V))‖
        ≤ R ^ 2 * ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin G))‖ := by
    rw [Matrix.l2_opNorm_toEuclideanCLM, Matrix.l2_opNorm_toEuclideanCLM] at hNorm
    rw [opNorm_toContinuousLinearMap_toEuclideanLin,
      opNorm_toContinuousLinearMap_toEuclideanLin, hRewrite]
    exact hNorm
  exact hEig.trans hNorm'
