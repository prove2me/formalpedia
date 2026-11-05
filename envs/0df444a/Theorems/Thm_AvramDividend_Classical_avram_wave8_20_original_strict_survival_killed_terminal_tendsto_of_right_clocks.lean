-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_strict_survival_killed_terminal_tendsto_of_right_clocks
-- name    : AvramDividend.Classical.avram_wave8_20_original_strict_survival_killed_terminal_tendsto_of_right_clocks
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:11:04.734369+00:00
-- url     : https://prove2.me/theorems/9386dddc-1fd8-4976-8fee-4dc289e4d13f
-- title:
--   Original strictly killed rightpayment HJB terminal converges along right-approach clocks before actual ruin
-- statement:
--   At any strictly surviving sample path time, if a sequence of physical times approaches that time from the right, the exact source discounted, positive-part postrightpayment candidate reward killed at ruin converges to its value at that time. This is a pathwise no-circularity bridge for applying the already Proved dominated-convergence theorem.
-- source:
--   Original Avram Proposition 4(i) exact strict-survival killed post-rightpayment discounted positive-part continuation. Uses Proved W8-20 source HJB pathwise rightcontinuity 634baba4 and eventual strict survival f77d306f, continuous time discount and positive part, and pinned Mathlib nhdsWithin convergence. No assertion at ruin or for left-approach through jumps; provides exact pointwise source premise for DCT 274b6f2c.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_strict_survival_killed_terminal_tendsto_of_right_clocks
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (q : ℝ) (ω : Ω) (t : ℝ≥0)
    (ht : (t : ℝ≥0∞) < ruinTime X x D ω)
    (τ : ℕ → ℝ≥0)
    (hτ : Filter.Tendsto τ Filter.atTop (𝓝 t))
    (hτRight : ∀ n, t ≤ τ n) :
    Filter.Tendsto
      (fun n : ℕ =>
        if (τ n : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n : ℝ))) *
            w (x + X.X (τ n) ω - rightLimit D (τ n) ω))
        else 0) Filter.atTop
      (𝓝 (max 0 (Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)))) := by sorry
