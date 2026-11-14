-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_reciprocal_query_fresh
-- name    : CountingLLL.ReciprocalTest.reciprocal_query_fresh
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:52:34.020134+00:00
-- url     : https://prove2.me/theorems/7c55e2fc-933b-470a-8852-3a2ce4679ca2
-- title:
--   Every ReciprocalTest reveal-machine query is fresh
-- statement:
--   For every encoded input array and every step of the reveal-machine representation of ReciprocalTest, if the next atomic step queries an entropy coordinate, that coordinate is not among those read earlier. This holds for oracle bits, fair bits and finite-uniform draws. It is a pathwise freshness invariant; the input law and complete algorithm output remain separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalReveal
open CountingLLL.ReciprocalTest CountingLLL.RevealMachine

theorem CountingLLL.ReciprocalTest.reciprocal_query_fresh (x : ReadIndex → ℕ) (n : ℕ) (a : ReadIndex)
    (h : readIndex (CountingLLL.RevealMachine.run revealProgram x initial n).1 = some a) :
    a ∉ (CountingLLL.RevealMachine.run revealProgram x initial n).2 := by sorry
