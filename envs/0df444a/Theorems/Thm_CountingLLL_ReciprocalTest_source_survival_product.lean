-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_source_survival_product
-- name    : CountingLLL.ReciprocalTest.source_survival_product
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:15:52.615192+00:00
-- url     : https://prove2.me/theorems/bdba53ef-6368-4f47-982b-fbb8ba69892a
-- title:
--   ReciprocalTest survival factors telescope
-- statement:
--   For every nonnegative integer $n$, the product of the return-test survival factors $\prod_{j=2}^{n+1}(1-1/j)$ equals $1/(n+1)$. This is the finite telescoping identity used to derive the conditional zero-output probability in the proof of Lemma 6.5.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Mathlib
open scoped BigOperators

theorem CountingLLL.ReciprocalTest.source_survival_product (n : ℕ) :
    (∏ i ∈ Finset.range n, (1 - 1 / ((i+2 : ℕ) : ℝ))) = 1 / ((n+1 : ℕ) : ℝ) := by sorry
