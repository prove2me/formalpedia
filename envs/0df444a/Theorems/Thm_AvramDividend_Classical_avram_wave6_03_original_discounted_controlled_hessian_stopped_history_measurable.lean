-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_discounted_controlled_hessian_stopped_history_measurable
-- name    : AvramDividend.Classical.avram_wave6_03_original_discounted_controlled_hessian_stopped_history_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T21:35:35.425513+00:00
-- url     : https://prove2.me/theorems/86942a34-b10b-47e8-bbd4-7afb45680497
-- title:
--   Actual discounted ruin-stopped controlled Hessian is measurable at each original right-continuous stopping time
-- statement:
--   The exact original-source HJB capped second derivative at the strict pre-dividend reserve left limit, multiplied by e^{-qt} and killed inclusively at the actual original ruin time and deterministic finite horizon, is measurable in the original right-continuous stopping-time sigma algebra when evaluated by stoppedValue at any original stopping time. Holds for arbitrary original sigma (including zero) and nu without a Brownian copy; follows from the Proved source-specific strongly predictable discounted Hessian and measurable_stoppedValue. This supplies the actual source predictable second-derivative cell weight needed for discounted Gaussian quadratic compensation, not the full Ito identity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_03_original_source_discounted_ruin_stopped_cap_hessian_predictable

open MeasureTheory ProbabilityTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_wave6_03_original_discounted_controlled_hessian_stopped_history_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hw : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ) (T : ℝ≥0)
    (τ : Ω → ℝ≥0)
    (hτ : IsStoppingTime 𝓕.rightCont (fun ω => (τ ω : WithTop ℝ≥0))) :
    Measurable[hτ.measurableSpace]
      (stoppedValue (fun t ω =>
        if t ≤ T then
          (Real.exp (-(q * (t : ℝ))) *
            (let y := Function.leftLim
                (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
             if 0 < y ∧ ENNReal.ofReal y < C then iteratedDeriv 2 w y else 0)) *
          (if (t : ℝ≥0∞) ≤ ruinTime X x D ω then (1 : ℝ) else 0)
        else 0) (fun ω => (τ ω : WithTop ℝ≥0))) := by
  sorry
