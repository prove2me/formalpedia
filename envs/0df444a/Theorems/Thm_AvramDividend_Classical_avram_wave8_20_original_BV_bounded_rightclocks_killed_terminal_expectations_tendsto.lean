-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_rightclocks_killed_terminal_expectations_tendsto
-- name    : AvramDividend.Classical.avram_wave8_20_original_BV_bounded_rightclocks_killed_terminal_expectations_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:18:52.003878+00:00
-- url     : https://prove2.me/theorems/22b447f6-88dd-49b3-bc9b-b845b0e03ffd
-- title:
--   Original bounded right-clock killed terminal expectations converge through strict ruin and positive-cap localisation
-- statement:
--   For a sequence of uniformly bounded measurable original physical clocks approaching an arbitrary measurable limit pathwise almost surely from the right, the expected strictly killed source BV terminal converges to the expected limit terminal. The result handles both pre-ruin right continuity and at/after ruin killing with only original assumptions, avoiding circular stochastic bounds.
-- source:
--   Exact original source strict-survival positive-part rightpayment terminal for arbitrary bounded measurable right-clock sequences. Apply the independently Proved pre-ruin raw right-clock continuity once available, original eventual survival f77d306f, Proved postruin zero 19babd50, and Proved noncircular dominated convergence 274b6f2c. In each source path split strict survival vs ruin; at first ruin the limit is zero, not a left-jump value. No assumption of terminal convergence or desired supermartingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_preruin_discounted_postpayment_positivepart_right_clock_limit
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postruin_right_clock_killed_terminal_tendsto_zero
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_eventually_strict_survival_of_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_BV_bounded_measurable_clocks_terminal_DCT
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave8_20_original_BV_bounded_rightclocks_killed_terminal_expectations_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (H : ℝ≥0) (t : Ω → ℝ≥0) (τ : ℕ → Ω → ℝ≥0)
    (hτMeas : ∀ n, Measurable (τ n))
    (hτBound : ∀ n ω, τ n ω ≤ H)
    (hRight : ∀ n ω, t ω ≤ τ n ω)
    (hRightTend : ∀ᵐ ω ∂P, Tendsto (fun n => τ n ω) atTop (𝓝 (t ω))) :
    Tendsto (fun n : ℕ => ∫ ω, (if (τ n ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (τ n ω : ℝ))) *
            w (x + X.X (τ n ω) ω - rightLimit D (τ n ω) ω))
        else 0) ∂P) atTop
      (𝓝 (∫ ω, (if (t ω : ℝ≥0∞) < ruinTime X x D ω then
          max 0 (Real.exp (-(q * (t ω : ℝ))) *
            w (x + X.X (t ω) ω - rightLimit D (t ω) ω))
        else 0) ∂P)) := by sorry
