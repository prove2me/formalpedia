-- Prove2me | Theorems.Thm_CountingLLL_RandomRAM_iid_first_exit
-- name    : CountingLLL.RandomRAM.iid_first_exit
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T06:50:12.885713+00:00
-- url     : https://prove2.me/theorems/67199934-9808-4550-adcd-90d97444a487
-- title:
--   First-exit probability for independent trials
-- statement:
--   Let independent trials have common law $\nu$, and let $S$ and $T$ be disjoint measurable events. Continue while trials fall in $S$, and succeed when the first trial outside $S$ lies in $T$. Then the success probability is $\nu(T)/(1-\nu(S))$, interpreted in extended nonnegative reals. This identity supplies the geometric-race calculation for the local Coin procedure of Algorithm 6.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Theorems.Thm_CountingLLL_RandomRAM_reciprocal_expected_cost
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.RandomRAM.iid_first_exit {β : Type} [MeasurableSpace β] (ν : Measure β) [IsProbabilityMeasure ν]
    (S T : Set β) (hS : MeasurableSet S) (hT : MeasurableSet T) (hst : Disjoint S T) :
    let μ := Measure.infinitePi fun _ : ℕ => ν
    μ {ω : ℕ → β | ∃ n, (∀ i < n, ω i ∈ S) ∧ ω n ∈ T} = ν T / (1 - ν S) := by sorry
