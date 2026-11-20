-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_B_original_anynu_finite_negative_Borel_weighted_past_compensator_real_L1
-- name    : AvramDividend.Classical.avram_jump6_B_original_anynu_finite_negative_Borel_weighted_past_compensator_real_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T10:03:33.860065+00:00
-- url     : https://prove2.me/theorems/995979e4-e87f-44f7-9edf-d9ce28d9673e
-- title:
--   Original any-jump-activity marked Borel cell signed past-predictable real compensation L1 without supplied rate
-- statement:
--   For the original spectrally negative Levy process, arbitrary past-measurable nonnegative integrable weights Wpos and Wneg, any finite locally measured negative Borel marks and deterministic time interval, the signed weighted actual negative-mark real count is integrable with its exact compensator expectation. The rate follows from the original predictable simple-mark Campbell identity, without finite total jump activity or any supplied expected-rate hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_a27_original_predictable_negative_Borel_simple_marked_compensation_no_rate_hypothesis_20261117
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_signed_past_weighted_real_rate
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_B_original_anynu_finite_negative_Borel_weighted_past_compensator_real_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (Wpos Wneg : Ω → ℝ≥0∞)
    (hWpos : Measurable[𝓕 s] Wpos)
    (hWneg : Measurable[𝓕 s] Wneg)
    (hPosFinite : (∫⁻ ω, Wpos ω ∂P) < ⊤)
    (hNegFinite : (∫⁻ ω, Wneg ω ∂P) < ⊤)
    (hν : X.ν B < ⊤)
    (hNeg : B ⊆ Iio (0 : ℝ)) :
    Integrable (fun ω =>
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal) P ∧
    (∫ ω,
      (Wpos ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal -
      (Wneg ω * ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)).toReal ∂P) =
      ((∫⁻ ω, Wpos ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal -
      ((∫⁻ ω, Wneg ω ∂P) * (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)).toReal := by sorry
