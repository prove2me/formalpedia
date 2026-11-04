-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
-- name    : AvramDividend.Classical.avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:14:30.468056+00:00
-- url     : https://prove2.me/theorems/be6ac215-7726-45be-8737-f5ef6524519e
-- title:
--   Original source ruin clock is the pathwise limit of bounded upper grid clocks with vanishing mesh error
-- statement:
--   For the same actual original spectrally negative Lévy process and the exact min(ruinTime,n).toNNReal clock, any sequence of sampled ceiling clocks bounded below by this true clock and above by this clock plus a vanishing nonnegative mesh converges pointwise to the true stopped clock. This is deterministic pathwise NNReal squeeze, a distinct prerequisite from stochastic-integral càdlàg or L1 convergence.
-- source:
--   Original min-ruin horizon clock from source residual 0dda1be7; Mathlib Filter squeeze and Tendsto.add for nonnegative real times.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- Original ruin-truncated stopped time is the limit of upper ceiling clocks with vanishing mesh error. -/
theorem AvramDividend.Classical.avram_p4_e_localise_original_ruin_grid_clock_squeeze_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (n : ℕ) (τ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω = (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (e : ℕ → ℕ → ℝ≥0) (K : ℕ → Ω → ℕ)
    (δ : ℕ → ℝ≥0) (hδ : Tendsto δ atTop (𝓝 0))
    (hLower : ∀ k ω, τ ω ≤ e k (K k ω))
    (hUpper : ∀ k ω, e k (K k ω) ≤ τ ω + δ k) :
    ∀ ω, Tendsto (fun k => e k (K k ω)) atTop (𝓝 (τ ω)) := by sorry
