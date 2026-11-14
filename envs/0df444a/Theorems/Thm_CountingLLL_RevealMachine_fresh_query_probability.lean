-- Prove2me | Theorems.Thm_CountingLLL_RevealMachine_fresh_query_probability
-- name    : CountingLLL.RevealMachine.fresh_query_probability
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:46:28.8532+00:00
-- url     : https://prove2.me/theorems/d3560f47-d346-4682-a272-e99049f1ef08
-- title:
--   Deferred decisions at a reveal-machine step
-- statement:
--   For a deterministic reveal machine running on an independent countable-valued array, consider an observable program-state event $R$ at a fixed step where a query is present. If, on that event, the queried coordinate has not previously been read and its designated coordinate event has probability $p$, then the probability of $R$ together with that coordinate event is $p$ times the probability of $R$. Coordinate laws may differ. This is a generic machine theorem; instantiating it for ReciprocalTest remains separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_RevealMachine
open MeasureTheory ProbabilityTheory CountingLLL.RevealMachine
open scoped ENNReal

theorem CountingLLL.RevealMachine.fresh_query_probability {σ ι α : Type*} [Countable ι] [DecidableEq ι]
    [MeasurableSpace α] [Countable α] [MeasurableSingletonClass α]
    (P : Program σ ι α) (initial : σ) (n : ℕ) (default : ι) (R : Set σ)
    (κ : ι → Measure α) [∀ i, IsProbabilityMeasure (κ i)]
    (A : ι → Set α) (hA : ∀ i, MeasurableSet (A i)) (p : ℝ≥0∞)
    (hfresh : ∀ ω, (run P ω initial n).1 ∈ R → (P.query (run P ω initial n).1).isSome →
      (P.query (run P ω initial n).1).getD default ∉ (run P ω initial n).2)
    (hsame : ∀ ω, (run P ω initial n).1 ∈ R → (P.query (run P ω initial n).1).isSome →
      κ ((P.query (run P ω initial n).1).getD default) (A ((P.query (run P ω initial n).1).getD default)) = p) :
    (Measure.infinitePi κ) {ω | (run P ω initial n).1 ∈ R ∧ (P.query (run P ω initial n).1).isSome ∧
      ω ((P.query (run P ω initial n).1).getD default) ∈ A ((P.query (run P ω initial n).1).getD default)} =
    (Measure.infinitePi κ) {ω | (run P ω initial n).1 ∈ R ∧ (P.query (run P ω initial n).1).isSome} * p := by sorry
