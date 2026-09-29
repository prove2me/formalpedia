-- Prove2me | solution 1 for off_diagonal_tangent_response_spectral_norm_bound
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-22T00:28:26.263132+00:00
-- url     : https://prove2.me/submissions/49321c5d-fc29-4994-8dd0-20a64d9d3b0f

import Theorems.Thm_off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier
import Theorems.Thm_tangent_diagonal_multiplier_spectral_norm_le_universal_multiple
import Theorems.Thm_tangent_projection_spectral_norm_le_universal_multiple
import Mathlib.Tactic

open MatrixCompletion

private lemma spectralNorm_sub_le
    {n₁ n₂ : ℕ} (X Y : Matrix (Fin n₁) (Fin n₂) ℝ) :
    spectralNorm (X - Y) ≤ spectralNorm X + spectralNorm Y := by
  unfold spectralNorm
  have hlin :
      LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin (X - Y)) =
        LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin X) -
          LinearMap.toContinuousLinearMap (Matrix.toEuclideanLin Y) := by
    ext v i
    simp [Matrix.toEuclideanLin]
  rw [hlin]
  exact norm_sub_le _ _

/-!
Source: Candes-Recht 2008, Section 6, PDF pp. 23--27.  Equation (6.1)
computes the tangent-coordinate kernel, equation (6.2) records its coherence
bounds, and Lemma 6.4 on PDF p. 27 bounds the diagonal tangent-kernel
multiplier.  The off-diagonal response used in equations (6.13)--(6.14) is the
same full tangent-kernel response with the diagonal multiplier omitted.

Reduction: write the off-diagonal response as
`P_T X - tangentDiagonalMultiplier X`, then apply the spectral-norm triangle
inequality, the universal spectral-norm bound for `P_T`, and the universal
spectral-norm bound for the diagonal tangent multiplier.
-/

theorem solution :
    ∃ Cresp : ℝ, 0 < Cresp ∧
      ∀ (n₁ n₂ r : ℕ) (M : Matrix (Fin n₁) (Fin n₂) ℝ)
        (μ₀ : ℝ) (S : SVD M r),
        0 < n₁ → 0 < n₂ → 0 < r →
        1 ≤ μ₀ → A0 S μ₀ →
        ∀ X : Matrix (Fin n₁) (Fin n₂) ℝ,
          spectralNorm (offDiagonalTangentResponse S X) ≤
            Cresp * spectralNorm X := by
  rcases tangent_projection_spectral_norm_le_universal_multiple with
    ⟨Ctangent, hCtangent, hTangent⟩
  rcases tangent_diagonal_multiplier_spectral_norm_le_universal_multiple with
    ⟨Cdiag, hCdiag, hDiag⟩
  refine ⟨Ctangent + Cdiag, by positivity, ?_⟩
  intro n₁ n₂ r M μ₀ S hn₁ hn₂ hr hμ₀ hA0 X
  rw [off_diagonal_tangent_response_eq_tangent_projection_sub_diagonal_multiplier]
  calc
    spectralNorm (tangentProjection S X - tangentDiagonalMultiplier S X)
        ≤ spectralNorm (tangentProjection S X) +
            spectralNorm (tangentDiagonalMultiplier S X) :=
        spectralNorm_sub_le _ _
    _ ≤ Ctangent * spectralNorm X + Cdiag * spectralNorm X :=
        add_le_add (hTangent n₁ n₂ r M S X)
          (hDiag n₁ n₂ r M μ₀ S X hn₁ hn₂ hr hμ₀ hA0)
    _ = (Ctangent + Cdiag) * spectralNorm X := by ring
