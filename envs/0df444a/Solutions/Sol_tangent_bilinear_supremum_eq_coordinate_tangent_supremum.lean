-- Prove2me | solution 1 for tangent_bilinear_supremum_eq_coordinate_tangent_supremum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T09:26:50.135634+00:00
-- url     : https://prove2.me/submissions/ac842a32-f381-4a5f-9303-2a8fb57e1865

import Definitions.Def_matrix_completion_talagrand_coordinate_tangent
import Theorems.Thm_tangent_sampling_fluctuation_vectorized_operator_representation
import Mathlib.Data.Matrix.Basic

open MatrixCompletion
open scoped Classical BigOperators Matrix

private theorem matrixInner_tangent_sampling_fluctuation_eq_coordinate_sum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ)
    (X1 X2 : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hT : tangentProjection S X2 = X2) :
    matrixInner X1 (tangentProjection S (samplingProjection Omega X2) - p • X2) =
      ∑ i : Fin n₁, ∑ j : Fin n₂,
        (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
          (matrixInner X1 (tangentProjection S (coordinateMatrix i j)) *
            matrixInner (tangentProjection S (coordinateMatrix i j)) X2)) := by
  classical
  let y : Fin n₁ × Fin n₂ → Matrix (Fin n₁) (Fin n₂) ℝ :=
    fun ab => tangentProjection S (coordinateMatrix ab.1 ab.2)
  let A : Matrix (Fin n₁ × Fin n₂) (Fin n₁ × Fin n₂) ℝ :=
    ∑ ab : Fin n₁ × Fin n₂,
      (((if ab ∈ Omega then (1 : ℝ) else 0) - p) •
        Matrix.vecMulVec
          (fun e : Fin n₁ × Fin n₂ => y ab e.1 e.2)
          (fun e : Fin n₁ × Fin n₂ => y ab e.1 e.2))
  have hrepr :=
    tangent_sampling_fluctuation_vectorized_operator_representation S Omega p X2 hT
  have hreprA :
      (fun e : Fin n₁ × Fin n₂ =>
        (tangentProjection S (samplingProjection Omega X2) - p • X2) e.1 e.2) =
        A.mulVec (fun e : Fin n₁ × Fin n₂ => X2 e.1 e.2) := by
    dsimp [A, y]
    exact hrepr
  have hdot : matrixInner X1
        (tangentProjection S (samplingProjection Omega X2) - p • X2) =
      ∑ e : Fin n₁ × Fin n₂,
        X1 e.1 e.2 * (A.mulVec (fun e : Fin n₁ × Fin n₂ => X2 e.1 e.2)) e := by
    unfold matrixInner
    change (∑ i : Fin n₁, ∑ j : Fin n₂,
        (fun e : Fin n₁ × Fin n₂ =>
          X1 e.1 e.2 *
            (tangentProjection S (samplingProjection Omega X2) - p • X2) e.1 e.2)
          (i, j)) =
      ∑ e : Fin n₁ × Fin n₂,
        X1 e.1 e.2 * (A.mulVec (fun e : Fin n₁ × Fin n₂ => X2 e.1 e.2)) e
    rw [← Fintype.sum_prod_type']
    change (∑ e : Fin n₁ × Fin n₂,
        X1 e.1 e.2 *
          (fun e : Fin n₁ × Fin n₂ =>
            (tangentProjection S (samplingProjection Omega X2) - p • X2) e.1 e.2) e) =
      ∑ e : Fin n₁ × Fin n₂,
        X1 e.1 e.2 * (A.mulVec (fun e : Fin n₁ × Fin n₂ => X2 e.1 e.2)) e
    rw [hreprA]
  rw [hdot]
  unfold A y
  simp only [Matrix.mulVec, dotProduct, Matrix.sum_apply, Matrix.smul_apply,
    Matrix.vecMulVec_apply, smul_eq_mul, Finset.sum_mul, Finset.mul_sum]
  let F : (Fin n₁ × Fin n₂) → (Fin n₁ × Fin n₂) →
      (Fin n₁ × Fin n₂) → ℝ :=
    fun e x ab =>
      X1 e.1 e.2 *
        (((if ab ∈ Omega then (1 : ℝ) else 0) - p) *
          (tangentProjection S (coordinateMatrix ab.1 ab.2) e.1 e.2 *
            tangentProjection S (coordinateMatrix ab.1 ab.2) x.1 x.2) *
            X2 x.1 x.2)
  change (∑ e : Fin n₁ × Fin n₂, ∑ x : Fin n₁ × Fin n₂,
      ∑ ab : Fin n₁ × Fin n₂, F e x ab) =
    ∑ i : Fin n₁, ∑ j : Fin n₂,
      ((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
        (matrixInner X1 (tangentProjection S (coordinateMatrix i j)) *
          matrixInner (tangentProjection S (coordinateMatrix i j)) X2)
  calc
    (∑ e : Fin n₁ × Fin n₂, ∑ x : Fin n₁ × Fin n₂,
        ∑ ab : Fin n₁ × Fin n₂, F e x ab)
        = ∑ e : Fin n₁ × Fin n₂, ∑ ab : Fin n₁ × Fin n₂,
            ∑ x : Fin n₁ × Fin n₂, F e x ab := by
          apply Finset.sum_congr rfl
          intro e _
          rw [Finset.sum_comm]
    _ = ∑ ab : Fin n₁ × Fin n₂, ∑ e : Fin n₁ × Fin n₂,
          ∑ x : Fin n₁ × Fin n₂, F e x ab := by
          rw [Finset.sum_comm]
    _ = ∑ i : Fin n₁, ∑ j : Fin n₂,
        ((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
          (matrixInner X1 (tangentProjection S (coordinateMatrix i j)) *
            matrixInner (tangentProjection S (coordinateMatrix i j)) X2) := by
          conv_rhs =>
            rw [← Fintype.sum_prod_type']
          apply Finset.sum_congr rfl
          intro ab _
          have hleft :
              (∑ e : Fin n₁ × Fin n₂, ∑ x : Fin n₁ × Fin n₂, F e x ab) =
                ((if ab ∈ Omega then (1 : ℝ) else 0) - p) *
                  (matrixInner X1 (tangentProjection S (coordinateMatrix ab.1 ab.2)) *
                    matrixInner (tangentProjection S (coordinateMatrix ab.1 ab.2)) X2) := by
            dsimp [F]
            unfold matrixInner
            conv_rhs =>
              rw [← Fintype.sum_prod_type']
              rw [← Fintype.sum_prod_type']
            simp_rw [Finset.sum_mul, Finset.mul_sum]
            ring_nf
            simp [mul_assoc, mul_left_comm, mul_comm]
          simpa using hleft

private theorem tangent_bilinear_value_eq_coordinate_tangent_sum
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ)
    (X1 X2 : Matrix (Fin n₁) (Fin n₂) ℝ)
    (hT : tangentProjection S X2 = X2) :
    p⁻¹ *
        matrixInner X1
          (tangentProjection S (samplingProjection Omega X2) - p • X2) =
      ∑ i : Fin n₁, ∑ j : Fin n₂,
        (((if (i, j) ∈ Omega then (1 : ℝ) else 0) - p) *
          tangentSamplingTalagrandCoefficient S p X1 X2 i j) := by
  rw [matrixInner_tangent_sampling_fluctuation_eq_coordinate_sum Omega S p X1 X2 hT]
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.mul_sum]
  apply Finset.sum_congr rfl
  intro j _
  simp [tangentSamplingTalagrandCoefficient]
  ring

/-- Coordinate expansion of the tangent-restricted bilinear sampling
fluctuation.

The left side is the bilinear expression obtained from Frobenius duality:
`p^{-1} <X1, P_T P_Omega X2 - p X2>`, with `X2` tangent.  This theorem expands
`P_Omega` in the coordinate basis and rewrites the result as the Appendix 9.1
coordinate sum while keeping the tangent restriction on `X2`.

Source: Candes--Recht, PDF p. 46, Appendix 9.1, immediately after equation
(9.2), where the tangent sampling deviation is expanded into the displayed
sum over matrix coordinates. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingTangentBilinearDeviation Omega S p =
      tangentSamplingCoordinateTangentSupremumDeviation Omega S p := by
  unfold tangentSamplingTangentBilinearDeviation
    tangentSamplingCoordinateTangentSupremumDeviation
  congr
  ext v
  constructor
  · intro hv
    rcases hv with ⟨X1, X2, hX1, hT, hX2, rfl⟩
    refine ⟨X1, X2, hX1, hT, hX2, ?_⟩
    exact tangent_bilinear_value_eq_coordinate_tangent_sum Omega S p X1 X2 hT
  · intro hv
    rcases hv with ⟨X1, X2, hX1, hT, hX2, rfl⟩
    refine ⟨X1, X2, hX1, hT, hX2, ?_⟩
    exact (tangent_bilinear_value_eq_coordinate_tangent_sum Omega S p X1 X2 hT).symm
