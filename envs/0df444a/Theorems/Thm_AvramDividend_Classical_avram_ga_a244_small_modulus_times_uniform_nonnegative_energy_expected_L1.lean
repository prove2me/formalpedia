-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a244_small_modulus_times_uniform_nonnegative_energy_expected_L1
-- name    : AvramDividend.Classical.avram_ga_a244_small_modulus_times_uniform_nonnegative_energy_expected_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:29:28.214577+00:00
-- url     : https://prove2.me/theorems/77f61199-42ca-4474-a597-c2d3bb6b1ebf
-- title:
--   Vanishing positive small-cell Taylor modulus multiplied by uniform integrable raw Gaussian energy gives expected L1 zero
-- statement:
--   For any measurable source with a nonnegative integrable finite-grid energy F bounded uniformly in expectation and any nonnegative scalar Taylor modulus ε_m tending to zero, the expected product ε_m F_m tends to zero. This is the small-increment analytic expectation mechanism for the original Gaussian full-cell one-sided positive Taylor and combined source a216, using exact original a240 uniform raw energy, not surrogate energy.
-- source:
--   Original Gaussian a194 small positive Taylor bound, a240 original full-cell raw quadratic expectation bound, and a190 compact Taylor modulus.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a244_small_modulus_times_uniform_nonnegative_energy_expected_L1
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (F : ℕ → Ω → ℝ) (ε : ℕ → ℝ) (K : ℝ)
    (hFI : ∀ m, Integrable (F m) P)
    (hFpos : ∀ m ω, 0 ≤ F m ω)
    (hBound : ∀ m, (∫ ω, F m ω ∂P) ≤ K)
    (hε : ∀ m, 0 ≤ ε m)
    (hεlim : Tendsto ε atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun m => ∫ ω, ε m * F m ω ∂P) atTop (𝓝 (0 : ℝ)) := by sorry
