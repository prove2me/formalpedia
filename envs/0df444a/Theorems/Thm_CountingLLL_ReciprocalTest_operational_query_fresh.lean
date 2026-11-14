-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_query_fresh
-- name    : CountingLLL.ReciprocalTest.operational_query_fresh
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:07:54.375113+00:00
-- url     : https://prove2.me/theorems/9e5efb1f-b4b8-4ad9-9d1e-f67e31d2310c
-- title:
--   Operational ReciprocalTest next query has its marginal law
-- statement:
--   Under the original independent entropy law, fix a step and an exact operational ReciprocalTest state $s$ whose next query is coordinate $a$. The probability of reaching $s$ and seeing the next encoded value in any set $U$ is the probability of reaching $s$ times the prescribed marginal probability of $U$ at $a$. This proves the one-step deferred-decisions property for oracle bits, fair bits, and finite-uniform draws; it does not itself prove the full output or expected-cost formula.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.operational_query_fresh (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s : State) (a : ReadIndex)
    (ha : readIndex s = some a) (U : Set ℕ) :
    entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ entropyCode ω a ∈ U} =
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s} * readLaw B a U := by sorry
