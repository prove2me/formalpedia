-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_paired_streams
-- name    : CountingLLL.ReciprocalTest.paired_streams
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:00:51.984216+00:00
-- url     : https://prove2.me/theorems/6ec936e0-e8ef-4973-8efe-068bb4611caf
-- title:
--   Pairing independent product streams
-- statement:
--   Let $(X_n)$ and $(Y_n)$ be independent sequences of independent identically distributed Boolean variables, with respective laws $\mu$ and $\nu$. Then the paired sequence $((X_n,Y_n))$ is an independent identically distributed sequence with common law $\mu\otimes\nu$. This reindexes the oracle and fair-bit entropy of Algorithm 6 into the trial-pair model of Coin.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, Algorithm 6, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open MeasureTheory ProbabilityTheory
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.paired_streams (μ ν : Measure Bool) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] :
    let μs := Measure.infinitePi fun _ : ℕ => μ
    let νs := Measure.infinitePi fun _ : ℕ => ν
    (μs.prod νs).map (fun p n => (p.1 n, p.2 n)) =
      Measure.infinitePi (fun _ : ℕ => μ.prod ν) := by sorry
