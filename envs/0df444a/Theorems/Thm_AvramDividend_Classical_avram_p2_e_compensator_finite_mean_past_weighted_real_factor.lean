-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_mean_past_weighted_real_factor
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_mean_past_weighted_real_factor
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:40:29.885842+00:00
-- url     : https://prove2.me/theorems/b38c4b95-f56e-4daf-8718-c2b3e536af9f
-- title:
--   Finite original intrinsic-count real mean factors from an arbitrary integrable past weight without a Levy-rate hypothesis
-- statement:
--   If the actual intrinsic marked count has finite first moment and a nonnegative original F_s measurable weight has finite mean, the real expectation of their product factors exactly into the real conversion of the product of their ENNReal means, without invoking any deterministic Levy rate. This isolates the stochastic independent-increment factorisation from the separate analytic intensity identification.
-- source:
--   P2-E proved original intrinsic rectangle count measurable (8146a449), P2-E proved intrinsic weighted factorisation (75e37892), pinned Mathlib integral_toReal and ENNReal.mul_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_intrinsic_rectangle_factor

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_mean_past_weighted_real_factor
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hWfinite : (∫⁻ ω, W ω ∂P) < ⊤)
    (hNfinite : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) < ⊤) :
    (∫ ω, (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      ((∫⁻ ω, W ω ∂P) * (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P)).toReal := by sorry
