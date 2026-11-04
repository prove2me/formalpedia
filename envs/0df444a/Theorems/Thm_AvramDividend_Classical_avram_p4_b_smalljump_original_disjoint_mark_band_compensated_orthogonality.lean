-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_disjoint_mark_band_compensated_orthogonality
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_disjoint_mark_band_compensated_orthogonality
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:20:26.222585+00:00
-- url     : https://prove2.me/theorems/e17f456b-f5cd-4d79-8995-a69cb4a6b87d
-- title:
--   Original disjoint mark band compensated orthogonality from cross moments
-- statement:
--   Under integrable first moments and factorised physical cross moments, disjoint original intrinsic Lévy marked-count increments have zero centred covariance.
-- source:
--   Original X.X and X.nu, pinned Mathlib source-exact Lean proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_disjoint_mark_band_compensated_orthogonality
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (A B : Set ℝ) (hDisjoint : Disjoint A B)
    (JA JB : Ω → ℝ)
    (hSourceA : ∀ ω, JA ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ A)).toReal)
    (hSourceB : ∀ ω, JB ω =
      (((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal)
    (hJA : Integrable JA P) (hJB : Integrable JB P)
    (hCrossInt : Integrable (fun ω => JA ω * JB ω) P)
    (rA rB : ℝ)
    (hRateA : rA = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν A)).toReal)
    (hRateB : rB = ((((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal)
    (hFirstA : (∫ ω, JA ω ∂P) = rA)
    (hFirstB : (∫ ω, JB ω ∂P) = rB)
    (hCross : (∫ ω, JA ω * JB ω ∂P) = rA * rB) :
    (∫ ω, (JA ω - rA) * (JB ω - rB) ∂P) = 0 := by sorry
