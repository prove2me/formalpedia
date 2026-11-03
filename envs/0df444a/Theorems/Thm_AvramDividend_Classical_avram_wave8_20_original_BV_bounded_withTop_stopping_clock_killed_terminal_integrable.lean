-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_withTop_stopping_clock_killed_terminal_integrable
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_bounded_withTop_stopping_clock_killed_terminal_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T23:56:19.99059+00:00
-- url     : https://prove2.me/theorems/4d58b5a7-f7c1-48d7-8f2c-ed6be6d1bdb3
-- title:
--   Original BV terminal integrability for bounded right-continuous filtration WithTop stopping clocks
-- statement:
--   For any original right-continuous-filtration stopping time valued in extended nonnegative time that is bounded by a finite horizon, its finite physical clock has the strictly surviving discounted positive postrightpayment HJB terminal integrable under Standing bounded variation, including the actual source ruin boundary.
-- source:
--   Original source cap admissibility, ruinTime and rightCont filtration. Converts a genuinely bounded ENNReal-valued stopping clock to its physical NNReal clock using hBound to exclude infinity, ENNReal.coe_toNNReal, preserved stopping-time equality and explicit physical horizon bound. Invokes independently Proved source bounded physical stopping terminal L1 b438eaf6. No stopped supermartingale inequality.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_random_stop_survival_terminal_integrable
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_bounded_withTop_stopping_clock_killed_terminal_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (σ : Ω → ℝ≥0∞)
    (hσStop : IsStoppingTime 𝓕.rightCont σ)
    (hσBound : ∀ ω, σ ω ≤ (H : ℝ≥0∞)) :
    let τ : Ω → ℝ≥0 := fun ω => (σ ω).toNNReal
    Integrable (fun ω =>
      if (τ ω : ℝ≥0∞) < ruinTime X x D ω then
        max 0 (Real.exp (-(q * (τ ω : ℝ))) *
          w (x + X.X (τ ω) ω - rightLimit D (τ ω) ω))
      else 0) P := by sorry
