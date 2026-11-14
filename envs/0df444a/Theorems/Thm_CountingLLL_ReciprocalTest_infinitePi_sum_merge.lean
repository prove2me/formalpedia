-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_infinitePi_sum_merge
-- name    : CountingLLL.ReciprocalTest.infinitePi_sum_merge
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:03:16.1879+00:00
-- url     : https://prove2.me/theorems/5b74afe2-462f-4642-8da2-1c673552b3cd
-- title:
--   Merging independent countable product arrays
-- statement:
--   Let two independent arrays each have their own countable index set and independent, possibly nonidentically distributed coordinates. Merging the arrays by tagging the two index sets has the independent product law on their disjoint union.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal BigOperators

theorem CountingLLL.ReciprocalTest.infinitePi_sum_merge {ι κ α : Type*} [Countable ι] [Countable κ]
    [MeasurableSpace α] (μ : ι → Measure α) (ν : κ → Measure α)
    [∀ i, IsProbabilityMeasure (μ i)] [∀ j, IsProbabilityMeasure (ν j)] :
    ((Measure.infinitePi μ).prod (Measure.infinitePi ν)).map
      (fun p : (ι → α) × (κ → α) => Sum.elim p.1 p.2) =
        Measure.infinitePi (Sum.elim μ ν) := by sorry
