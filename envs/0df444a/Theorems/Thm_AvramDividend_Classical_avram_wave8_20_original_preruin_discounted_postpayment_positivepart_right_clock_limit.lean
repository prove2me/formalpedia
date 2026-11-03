-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_discounted_postpayment_positivepart_right_clock_limit
-- name    : AvramDividend.Classical.avram_wave8_20_original_preruin_discounted_postpayment_positivepart_right_clock_limit
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:01:12.913539+00:00
-- url     : https://prove2.me/theorems/95b76f5b-38d9-4e81-84c0-57a4e5d83a0d
-- title:
--   Original strict-preruin discounted postrightpayment positive-part continuity along right clocks
-- statement:
--   At any original finite strictly surviving physical time, the discounted postrightpayment HJB positive part has the expected right-clock limit for every sequence of nonnegative physical clocks approaching from the right, including paths with later jumps.
-- source:
--   Direct source-specific continuity consequence of previously Proved original postrightpayment C0 right continuity 634baba4 and eventually strict survival f77d306f. Restrict to the source right-neighborhood set t≤s<ruin and apply ContinuousWithinAt of discounted positive part plus Tendsto in nhdsWithin. This lemma intentionally concerns the raw positive part; the separate killed-postruin zero helper 19babd50 handles ruin. No stochastic supermartingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_HJB_postpayment_rightContinuous
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_preruin_discounted_postpayment_positivepart_right_clock_limit
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
      (fun n : ℕ => max 0 (Real.exp (-(q * (τ n : ℝ))) *
        w (x + X.X (τ n) ω - rightLimit D (τ n) ω)))
      Filter.atTop
      (𝓝 (max 0 (Real.exp (-(q * (t : ℝ))) *
        w (x + X.X t ω - rightLimit D t ω)))) := by sorry
