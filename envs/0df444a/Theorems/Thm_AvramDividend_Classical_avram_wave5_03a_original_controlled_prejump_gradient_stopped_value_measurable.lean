-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
-- name    : AvramDividend.Classical.avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T19:37:30.40783+00:00
-- url     : https://prove2.me/theorems/efffb79c-b97f-4993-91ed-41c53f0621ff
-- title:
--   Actual controlled prepayment gradient at an original right-continuous stop is stopped-history measurable
-- statement:
--   For the actual spectrally negative Levy source X with any sigma and nu, an admissible dividend strategy D, smooth interior HJB test w, finite cap and an original right-continuous filtration stopping time tau, the standard stoppedValue of the original prepayment-reserve capped gradient is measurable for the stopped-time sigma-algebra. This follows via its canonically Proved strong predictability, strong progressivity and pinned Mathlib measurable_stoppedValue. It is a direct genuine predictable-integrand interface to the Gaussian martingale simple-cell lemmas and assumes neither nu=0 nor nonzero sigma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04b_controlled_prejump_cap_gradient_stronglyPredictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave5_03a_original_controlled_prejump_gradient_stopped_value_measurable
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
        if 0 < y ∧ ENNReal.ofReal y < C then deriv w y else 0)
        (fun ω => (τ ω : WithTop ℝ≥0))) := by
  sorry
