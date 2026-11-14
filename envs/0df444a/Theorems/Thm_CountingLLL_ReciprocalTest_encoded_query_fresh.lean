-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_encoded_query_fresh
-- name    : CountingLLL.ReciprocalTest.encoded_query_fresh
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:58:58.583671+00:00
-- url     : https://prove2.me/theorems/d657eb8c-256e-4c01-bb82-4acec48b0ba1
-- title:
--   ReciprocalTest next query has its marginal law
-- statement:
--   Under the independent encoded input law, at any fixed step and on any exact state $s$ whose next query is coordinate $a$, the event that the next value belongs to a set $U$ has probability equal to the state probability times the marginal probability assigned to $U$ at $a$. This covers adaptive oracle bits, fair bits and uniform draws. Equality with the original entropy law and the full execution distribution remain separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.encoded_query_fresh (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) (s : State) (a : ReadIndex)
    (ha : readIndex s = some a) (U : Set ℕ) :
    encodedEntropyLaw B {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s ∧ x a ∈ U} =
      encodedEntropyLaw B {x | (CountingLLL.RevealMachine.run revealProgram x initial n).1 = s} * readLaw B a U := by sorry
