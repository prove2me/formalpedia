-- Prove2me | Theorems.Thm_CountingLLL_RevealMachine_history_fresh_query
-- name    : CountingLLL.RevealMachine.history_fresh_query
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:31:29.042606+00:00
-- url     : https://prove2.me/theorems/1c06f64c-b3b3-4664-b181-69aa006c01ae
-- title:
--   A fresh adaptive query remains independent of the execution history
-- statement:
--   Consider a deterministic reveal machine driven by independent countable-valued coordinates. Fix a time, a coordinate, and an arbitrary event determined by the entire state history up to that time. On the portion of that event where the next query is the fixed coordinate, suppose the coordinate has not already been read. Then its next value has its original marginal distribution even when conditioned on the entire history and the query choice. The displayed identity is valid without dividing by the probability of the conditioning event.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5. This is a general adaptive-reveal foundation for a rigorous coupling of the sampler, not a statement of the paper’s cost bound.

import Definitions.Def_CountingLLL_RevealMachine
open MeasureTheory ProbabilityTheory CountingLLL.RevealMachine
open scoped ENNReal

theorem CountingLLL.RevealMachine.history_fresh_query {σ ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (P : Program σ ι α) (init : σ) (n : ℕ) (a : ι)
    (H : (Fin (n+1) → σ) → Prop) (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (U : Set α) (hU : MeasurableSet U)
    (hfresh : ∀ ω, H (fun j => (run P ω init j.val).1) → P.query (run P ω init n).1 = some a →
      a ∉ (run P ω init n).2) :
    (Measure.infinitePi κ) {ω | H (fun j => (run P ω init j.val).1) ∧
      P.query (run P ω init n).1 = some a ∧ ω a ∈ U} =
      (Measure.infinitePi κ) {ω | H (fun j => (run P ω init j.val).1) ∧
      P.query (run P ω init n).1 = some a} * κ a U := by sorry
