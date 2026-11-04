-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_finite_weighted_count_real_mean
-- name    : AvramDividend.Classical.avram_p2_e_compensator_finite_weighted_count_real_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T12:25:40.463403+00:00
-- url     : https://prove2.me/theorems/fe933b18-eff1-4530-99f0-59c197fb47bf
-- title:
--   Original weighted finite-rate marked count has exact real-valued predictable mean
-- statement:
--   On the genuine original spectrally negative Lévy probability space, any nonnegative F_s-measurable weight of finite expectation times a finite-ν-rate intrinsic marked jump count has real expectation equal to the real conversion of E[W](t-s)ν(B), assuming the independent original unconditional rate. This extends the accepted ENNReal past factorisation to signed-integral-compatible real first moments, without requiring bounded weights, Poisson replacement, or the canonical compensated martingale as input.
-- source:
--   P2-E Proved source measurability 8146a449 and weighted rate factor e13617a2; pinned Mathlib ae_lt_top, integral_toReal, ENNReal.mul_lt_top.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_weighted_rate_from_unconditional

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_finite_weighted_count_real_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (W : Ω → ℝ≥0∞) (hW : Measurable[𝓕 s] W)
    (hWfinite : (∫⁻ ω, W ω ∂P) < ⊤)
    (hν : X.ν B < ⊤)
    (hRate : (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) = (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)) :
    (∫ ω, (W ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      ((∫⁻ ω, W ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by sorry
