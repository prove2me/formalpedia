-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_rightContinuous_lintegral_of_real_pathwise_with_envelope
-- name    : AvramDividend.Classical.chat04_rightContinuous_lintegral_of_real_pathwise_with_envelope
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:57:51.484978+00:00
-- url     : https://prove2.me/theorems/5eb61209-3408-49c8-809c-827cdcbad77c
-- title:
--   Right-continuity of an ENNReal expectation from right-continuous real trajectories and a uniform envelope
-- statement:
--   A family of real-valued random rewards that is pathwise right-continuous and eventually measurable has right-continuous extended-nonnegative expectation whenever it is eventually dominated by one integrable extended-nonnegative envelope. This bridges the pathwise killed Lévy scale payoff result and dominated convergence for its expected value.
-- source:
--   Mathlib tendsto_lintegral_filter_of_dominated_convergence' and continuous ENNReal.ofReal, pinned revision.

import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Mathlib.Topology.Order.LeftRightNhds

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_rightContinuous_lintegral_of_real_pathwise_with_envelope
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (g : NNReal → Ω → ℝ) (t : NNReal) (envelope : Ω → ENNReal)
    (hpath : ∀ ω, ContinuousWithinAt (fun u => g u ω) (Ici t) t)
    (hmeas : ∀ᶠ u in 𝓝[Ici t] t,
      AEMeasurable (fun ω => ENNReal.ofReal (g u ω)) P)
    (hbound : ∀ᶠ u in 𝓝[Ici t] t,
      ∀ᵐ ω ∂P, ENNReal.ofReal (g u ω) ≤ envelope ω)
    (hfin : (∫⁻ ω, envelope ω ∂P) ≠ ⊤) :
    ContinuousWithinAt
      (fun u => ∫⁻ ω, ENNReal.ofReal (g u ω) ∂P)
      (Ici t) t := by sorry
