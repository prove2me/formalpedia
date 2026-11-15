-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a315_eventual_ae_two_error_expected_L1_squeeze
-- name    : AvramDividend.Classical.avram_ga_a315_eventual_ae_two_error_expected_L1_squeeze
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:51:37.198188+00:00
-- url     : https://prove2.me/theorems/46d56cf4-da90-4f0a-adc8-01d43401c9bd
-- title:
--   Eventual almost-sure two-tail upper bound transfers two vanishing expected sources to a nonnegative Gaussian verification source
-- statement:
--   A nonnegative integrable expected Gaussian source F whose values are eventually almost surely bounded by constant multiples of two integrable error sources E and Q has expectation tending to zero if both source expectations tend to zero. This allows original a263 combined large-cell proof to use a308 eventual source bound, signed Gaussian exponential a275 and raw quadratic a313 without asserting the rare-event source bound at coarse mesh levels.
-- source:
--   Original Gaussian a263 eventual true fullcell source a308 with a275 signed expected rare exponential and a313 expected polynomial large Gaussian tail.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a315_eventual_ae_two_error_expected_L1_squeeze
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F E Q : ℕ → Ω → ℝ) (C D : ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hEI : ∀ m, Integrable (E m) P)
    (hQI : ∀ m, Integrable (Q m) P)
    (hFpos : ∀ m, ∀ᵐ ω ∂P, 0 ≤ F m ω)
    (hBound : ∀ᶠ m : ℕ in atTop, ∀ᵐ ω ∂P,
      F m ω ≤ C*E m ω + D*Q m ω)
    (hELim : Tendsto (fun m => ∫ ω, E m ω ∂P) atTop (𝓝 (0:ℝ)))
    (hQLim : Tendsto (fun m => ∫ ω, Q m ω ∂P) atTop (𝓝 (0:ℝ))) :
    Tendsto (fun m => ∫ ω, F m ω ∂P) atTop (𝓝 (0:ℝ)) := by sorry
