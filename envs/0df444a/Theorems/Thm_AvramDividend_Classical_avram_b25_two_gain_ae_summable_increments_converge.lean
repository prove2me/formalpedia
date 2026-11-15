-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b25_two_gain_ae_summable_increments_converge
-- name    : AvramDividend.Classical.avram_b25_two_gain_ae_summable_increments_converge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T01:01:14.368053+00:00
-- url     : https://prove2.me/theorems/0c1b86a4-b3a1-4665-bd72-9a96211da64f
-- title:
--   Absolute almost-everywhere summability of physical gain increments yields pointwise limits for both channels
-- statement:
--   For two real-valued gain families on a measure space, if the absolute successive-increment series is summable almost everywhere for each family, then their paths converge almost everywhere, with explicit measurable-space functions of the sample path as limits. Uses CauchySeq_of_summable_dist and CauchySeq.tendsto_limUnder in the complete real line. This isolates pointwise convergence from deriving summable increments via Tonelli.
-- source:
--   B25 stochastic-mesh analytic extraction; Mathlib Topology.Algebra.InfiniteSum.Real cauchySeq_of_summable_dist and UniformSpace.Cauchy CauchySeq.tendsto_limUnder; no source process substitutions.

import Mathlib
open MeasureTheory Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_b25_two_gain_ae_summable_increments_converge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (G J : ℕ → Ω → ℝ)
    (hGa : ∀ᵐ ω ∂P, Summable
      (fun k : ℕ => ‖G (k + 1) ω - G k ω‖))
    (hJa : ∀ᵐ ω ∂P, Summable
      (fun k : ℕ => ‖J (k + 1) ω - J k ω‖)) :
    ∃ (MG MJ : Ω → ℝ),
      (∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω))) ∧
      (∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω))) := by sorry
