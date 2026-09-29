-- Prove2me | solution 1 for tangent_bilinear_supremum_le_nested_dual_supremum
-- status  : ACCEPTED   (prove)
-- author  : @Shuze Chen
-- created : 2026-06-25T08:21:57.026627+00:00
-- url     : https://prove2.me/submissions/3da4768c-90d6-489e-8fa2-905f0b9d7113

import Theorems.Thm_tangent_bilinear_deviation_candidates_bddAbove

open MatrixCompletion
open scoped Classical BigOperators

/-- Embed each admissible bilinear pair into the nested supremum.

Source: Candes-Recht 2008, Appendix 9.1, PDF p. 46, immediately after equation
(9.2).  This is the reverse formal `sSup` bookkeeping for the display rewriting
`Z` as a supremum over two test matrices. -/
theorem solution
    {n₁ n₂ r : ℕ} {M : Matrix (Fin n₁) (Fin n₂) ℝ}
    (Omega : Finset (Fin n₁ × Fin n₂)) (S : SVD M r) (p : ℝ) :
    tangentSamplingTangentBilinearDeviation Omega S p ≤
      tangentSamplingNestedDualDeviation Omega S p := by
  unfold tangentSamplingTangentBilinearDeviation tangentSamplingNestedDualDeviation
  let bilinearSet : Set ℝ := {v : ℝ |
      ∃ X1 X2 : Matrix (Fin n₁) (Fin n₂) ℝ,
        frobeniusNorm X1 ≤ 1 ∧
          tangentProjection S X2 = X2 ∧
            frobeniusNorm X2 ≤ 1 ∧
              v =
                p⁻¹ *
                  matrixInner X1
                    (tangentProjection S (samplingProjection Omega X2) - p • X2)}
  have hbil_bdd : BddAbove bilinearSet := by
    simpa [bilinearSet] using tangent_bilinear_deviation_candidates_bddAbove Omega S p
  have hinner_bdd : ∀ X2 : Matrix (Fin n₁) (Fin n₂) ℝ,
      tangentProjection S X2 = X2 → frobeniusNorm X2 ≤ 1 →
      BddAbove {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
        frobeniusNorm X1 ≤ 1 ∧
          w = p⁻¹ * matrixInner X1
            (tangentProjection S (samplingProjection Omega X2) - p • X2)} := by
    intro X2 hT hX2
    rcases hbil_bdd with ⟨B, hB⟩
    refine ⟨B, ?_⟩
    intro w hw
    rcases hw with ⟨X1, hX1, rfl⟩
    exact hB ⟨X1, X2, hX1, hT, hX2, rfl⟩
  have houter_bdd : BddAbove {v : ℝ |
      ∃ X2 : Matrix (Fin n₁) (Fin n₂) ℝ,
        tangentProjection S X2 = X2 ∧
          frobeniusNorm X2 ≤ 1 ∧
            v =
              sSup {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
                frobeniusNorm X1 ≤ 1 ∧
                  w = p⁻¹ * matrixInner X1
                    (tangentProjection S (samplingProjection Omega X2) - p • X2)}} := by
    refine ⟨sSup bilinearSet, ?_⟩
    intro v hv
    rcases hv with ⟨X2, hT, hX2, rfl⟩
    refine csSup_le ?inner_nonempty ?inner_le
    · refine ⟨0, ?_⟩
      refine ⟨0, ?_, ?_⟩
      · unfold frobeniusNorm frobeniusNormSq
        simp
      · simp [matrixInner]
    · intro w hw
      rcases hw with ⟨X1, hX1, rfl⟩
      refine le_csSup hbil_bdd ?_
      exact ⟨X1, X2, hX1, hT, hX2, rfl⟩
  refine csSup_le ?bilinear_nonempty ?bilinear_le
  · refine ⟨0, ?_⟩
    refine ⟨0, 0, ?_, ?_, ?_, ?_⟩
    · unfold frobeniusNorm frobeniusNormSq
      simp
    · ext i j
      simp [tangentProjection, leftSingularProjection, rightSingularProjection,
        twoSidedSingularProjection]
    · unfold frobeniusNorm frobeniusNormSq
      simp
    · simp [matrixInner]
  · intro b hb
    rcases hb with ⟨X1, X2, hX1, hT, hX2, rfl⟩
    have hto_inner :
        p⁻¹ * matrixInner X1
          (tangentProjection S (samplingProjection Omega X2) - p • X2) ≤
        sSup {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
          frobeniusNorm X1 ≤ 1 ∧
            w = p⁻¹ * matrixInner X1
              (tangentProjection S (samplingProjection Omega X2) - p • X2)} := by
      refine le_csSup (hinner_bdd X2 hT hX2) ?_
      exact ⟨X1, hX1, rfl⟩
    have hto_outer :
        sSup {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
          frobeniusNorm X1 ≤ 1 ∧
            w = p⁻¹ * matrixInner X1
              (tangentProjection S (samplingProjection Omega X2) - p • X2)} ≤
        sSup {v : ℝ | ∃ X2 : Matrix (Fin n₁) (Fin n₂) ℝ,
          tangentProjection S X2 = X2 ∧
            frobeniusNorm X2 ≤ 1 ∧
              v =
                sSup {w : ℝ | ∃ X1 : Matrix (Fin n₁) (Fin n₂) ℝ,
                  frobeniusNorm X1 ≤ 1 ∧
                    w = p⁻¹ * matrixInner X1
                      (tangentProjection S (samplingProjection Omega X2) - p • X2)}} := by
      refine le_csSup houter_bdd ?_
      exact ⟨X2, hT, hX2, rfl⟩
    exact le_trans hto_inner hto_outer
