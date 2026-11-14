-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_return_probability_sup
-- name    : CountingLLL.ReciprocalTest.return_probability_sup
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:15:39.802517+00:00
-- url     : https://prove2.me/theorems/baf25250-caa6-4c9a-b141-8366692154a0
-- title:
--   Operational return probability is the supremum of finite-step probabilities
-- statement:
--   For either output bit, the operational ReciprocalTest return probability equals the supremum over $n$ of the probability that the machine is in the corresponding done state after $n$ steps. Done states are absorbing, so the finite-step events are increasing. This connects the finite-step state-distribution recursion to eventual output probabilities.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalTest
open MeasureTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.return_probability_sup (B : ℝ≥0∞) (b : Bool) :
    entropyLaw B {ω | Returns ω b} = ⨆ n : ℕ, entropyLaw B {ω | (run ω n).phase = .done b} := by sorry
