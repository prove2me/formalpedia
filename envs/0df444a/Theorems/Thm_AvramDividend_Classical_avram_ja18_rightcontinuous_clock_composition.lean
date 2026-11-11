-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_rightcontinuous_clock_composition
-- name    : AvramDividend.Classical.avram_ja18_rightcontinuous_clock_composition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T21:16:40.819359+00:00
-- url     : https://prove2.me/theorems/6feb2df6-1bf8-4768-a3aa-cea454299445
-- title:
--   Original right-continuous source values converge along decreasing ceiling clocks
-- statement:
--   For actual original-path reward field J with right-continuity on an almost-sure event, any sequence of times lying above the original clock and converging to that clock yields an almost surely convergent sequence of original reward values. No martingale assumption or stochastic process replacement is needed.
-- source:
--   Source-faithful isolated pathwise limit needed after finite-grid stopping for Open 2d92580d. Apply tendsto_nhdsWithin_iff to the upper-time ceiling events, then source right-continuity.

import Mathlib
open MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_rightcontinuous_clock_composition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    (J : ℝ≥0 → Ω → ℝ) (τ : Ω → ℝ≥0)
    (ρ : ℕ → Ω → ℝ≥0)
    (hRight : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      ContinuousWithinAt (fun u : ℝ≥0 => J u ω) (Set.Ici t) t)
    (hCeil : ∀ k ω, τ ω ≤ ρ k ω)
    (hConv : ∀ ω, Tendsto (fun k => ρ k ω) atTop (𝓝 (τ ω))) :
    ∀ᵐ ω ∂P, Tendsto (fun k => J (ρ k ω) ω) atTop (𝓝 (J (τ ω) ω)) := by sorry
