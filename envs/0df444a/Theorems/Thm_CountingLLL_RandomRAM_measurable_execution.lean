-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_measurable_execution
-- name    : CountingLLL.RandomRAM.measurable_execution
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T05:04:27.252623+00:00
-- url     : https://prove2.me/theorems/73429337-f84f-450d-8bd6-88c50c4da887
-- title:
--   Measurability of randomized oracle RAM execution
-- statement:
--   For any program and initial state of the fair-bit CSP oracle RAM, the event of termination is measurable, as is every event determined by the first-halt state (including its specified default on divergence). Oracle cost and running time, with infinite cost assigned to divergence, are measurable extended-nonnegative-real random variables. Individual assignment-output events and the counting-success event are measurable. The result ensures that the probability and expected-cost expressions used in the randomized counting and sampling targets have their standard measure-theoretic meaning.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovasz Local Lemma, STOC 2027 submission #442, Theorems 1.3 and 1.4 (PDF p.4) and Section 2.5 (PDF p.8), https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_RandomSpec
open MeasureTheory
open scoped ENNReal Classical
open CountingLLL.RandomRAM

theorem CountingLLL.RandomRAM.measurable_execution :
    (∀ (Φ : CSP) (P : Program) (s : State),
      MeasurableSet {ω | Halts Φ P ω s} ∧
      (∀ A : State → Prop, MeasurableSet {ω | A (finalState Φ P ω s)}) ∧
      Measurable (fun ω => oracleCost Φ P ω s) ∧
      Measurable (fun ω => timeCost Φ P ω s) ∧
      (∀ x : Φ.Config, MeasurableSet {ω | Halts Φ P ω s ∧
        OutputConfig Φ (finalState Φ P ω s) x})) ∧
    (∀ (Φ : CSP) (P : Program) (n : ℕ), MeasurableSet (countSuccess Φ P n)) := by sorry
