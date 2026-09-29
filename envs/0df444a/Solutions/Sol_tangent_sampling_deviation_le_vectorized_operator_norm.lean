-- Prove2me | solution 1 for tangent_sampling_deviation_le_vectorized_operator_norm
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-24T17:05:27.538156+00:00
-- url     : https://prove2.me/submissions/c53f0f28-2d25-42ab-9907-8845cee0a266

import Definitions.Def_matrix_completion_tangent
import Theorems.Thm_tangent_sampling_fluctuation_vectorized_operator_representation
import Mathlib.Analysis.CStarAlgebra.Matrix
import Mathlib.Analysis.InnerProductSpace.PiL2

open MatrixCompletion
open scoped BigOperators Matrix Classical Matrix.Norms.L2Operator

/-- Source: Candès-Recht arXiv:0805.4471, §4.2, equations (4.6)--(4.9),
and Rudelson's selection theorem setup. This is the `sSup ≤ operator norm`
wrapper after vectorizing the rank-one fluctuation operator. -/
theorem solution
    {n1 n2 r : Nat} {M : RealMatrix n1 n2} (S : SVD M r)
    (Omega : Finset (Fin n1 × Fin n2)) (p : Real) (hp : 0 ≤ p⁻¹) :
    tangentSamplingDeviation Omega S p
      ≤ p⁻¹ * ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin
          (∑ ab : Fin n1 × Fin n2,
            (((if ab ∈ Omega then (1 : Real) else 0) - p) •
              Matrix.vecMulVec
                (fun e : Fin n1 × Fin n2 =>
                  tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
                (fun e : Fin n1 × Fin n2 =>
                  tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)))))‖ := by
  classical
  set A : Matrix (Fin n1 × Fin n2) (Fin n1 × Fin n2) ℝ :=
    ∑ ab : Fin n1 × Fin n2,
      (((if ab ∈ Omega then (1 : Real) else 0) - p) •
        Matrix.vecMulVec
          (fun e : Fin n1 × Fin n2 =>
            tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)
          (fun e : Fin n1 × Fin n2 =>
            tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2)) with hA
  have hopA : ‖(LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin A))‖ = ‖A‖ := by
    rw [Matrix.l2_opNorm_def]; rfl
  rw [hopA]
  have hbridge : ∀ Y : RealMatrix n1 n2,
      frobeniusNorm Y
        = ‖(EuclideanSpace.equiv (Fin n1 × Fin n2) ℝ).symm (fun e => Y e.1 e.2)‖ := by
    intro Y
    rw [EuclideanSpace.norm_eq]
    unfold frobeniusNorm
    congr 1
    simp only [frobeniusNormSq, Real.norm_eq_abs, sq_abs, Fintype.sum_prod_type]
    rfl
  unfold tangentSamplingDeviation
  apply Real.sSup_le
  · rintro v ⟨X, hX, hXnorm, rfl⟩
    have hcore :
        frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
          ≤ ‖A‖ * frobeniusNorm X := by
      set v : EuclideanSpace ℝ (Fin n1 × Fin n2) :=
        (EuclideanSpace.equiv (Fin n1 × Fin n2) ℝ).symm (fun e => X e.1 e.2) with hv
      have hvof : v.ofLp = (fun e => X e.1 e.2) := rfl
      have hXeq : frobeniusNorm X = ‖v‖ := hbridge X
      have hfluct :
          frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
            = ‖(EuclideanSpace.equiv (Fin n1 × Fin n2) ℝ).symm
                (A *ᵥ v.ofLp)‖ := by
        rw [hbridge (tangentProjection S (samplingProjection Omega X) - p • X)]
        rw [hvof]
        congr 2
        rw [hA]
        exact tangent_sampling_fluctuation_vectorized_operator_representation S Omega p X hX
      rw [hfluct, hXeq]
      exact Matrix.l2_opNorm_mulVec A v
    have hAnn : 0 ≤ ‖A‖ := norm_nonneg _
    have hle : frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
        ≤ ‖A‖ := by
      calc frobeniusNorm (tangentProjection S (samplingProjection Omega X) - p • X)
            ≤ ‖A‖ * frobeniusNorm X := hcore
        _ ≤ ‖A‖ * 1 := by
              apply mul_le_mul_of_nonneg_left hXnorm hAnn
        _ = ‖A‖ := by ring
    apply mul_le_mul_of_nonneg_left hle hp
  · exact mul_nonneg hp (norm_nonneg _)
