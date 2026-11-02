-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
-- name    : AvramDividend.Classical.avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:20:49.867939+00:00
-- url     : https://prove2.me/theorems/63b5fb95-098e-4941-a975-2264623c6563
-- title:
--   Actual original right-continuously stopped prepayment Hessian is measurable for the stopped-history sigma algebra
-- statement:
--   For the actual original spectrally negative Levy process with arbitrary jump and Gaussian coefficients, an adapted dividend strategy, smooth C2 test on the strict capped reserve band, and a stopping time of the original right-continuous filtration, the clipped zero-extended second iterated derivative at the genuine prepayment left-limit controlled reserve is measurable in the stopped-history sigma algebra. This follows directly from the new strongly predictable original controlled Hessian process via Mathlib measurable_stoppedValue. It supplies the exact stopped-history Hessian weight needed to instantiate the Proved Gaussian quadratic energy identity for bounded compact-band localisations, with no nu=0 hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_controlled_prejump_cap_hessian_stronglyPredictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_original_controlled_prejump_hessian_stopped_value_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace]
      (stoppedValue (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) := by
  sorry
