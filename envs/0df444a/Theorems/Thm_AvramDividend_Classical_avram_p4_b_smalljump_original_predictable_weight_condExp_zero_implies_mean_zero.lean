-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:30:06.872166+00:00
-- url     : https://prove2.me/theorems/3b562cdb-f5d8-4fb2-8573-1a1e3956fffe
-- title:
--   Original Lévy centred randomly weighted finite-band source count has zero mean
-- statement:
--   For the exact original Lévy finite-band marked jump count and a genuinely random coefficient, zero conditional expectation of its real centred integral under the source right-continuous filtration and integrability imply zero unconditional mean. The original right-continuous trimmed probability is automatically sigma-finite, so the actual source conditional expectation integrates to its original-space mean.
-- source:
--   Accepted original right-continuous trim sigma-finiteness 159a9398; Mathlib integral_condExp and integral_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_rightcont_probability_trim_sigmaFinite

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (B : Set ℝ) (J : Ω → ℝ≥0∞)
    (hJsource : ∀ ω, J ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc s t ×ˢ B))
    (rate : ℝ≥0∞) (H : Ω → ℝ)
    (hInt : Integrable (fun ω =>
      H ω * ((J ω).toReal - rate.toReal)) P)
    (hCenter : P[(fun ω => H ω *
      ((J ω).toReal - rate.toReal)) | 𝓕.rightCont s] =ᵐ[P] 0) :
    (∫ ω, H ω * ((J ω).toReal - rate.toReal) ∂P) = 0 := by sorry
