-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_reciprocal_reveal_simulates
-- name    : CountingLLL.ReciprocalTest.reciprocal_reveal_simulates
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T09:50:01.268647+00:00
-- url     : https://prove2.me/theorems/0a5b1258-1a1c-4b9c-be32-23845f90a9f5
-- title:
--   Reveal-machine encoding simulates every ReciprocalTest step
-- statement:
--   For every machine entropy tape and every finite step count, the program-state component of the generic reveal-machine encoding of ReciprocalTest equals the state of the original small-step operational model. This establishes deterministic simulation only; preservation of the entropy law and freshness of the next queried coordinate remain separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalReveal
open CountingLLL.ReciprocalTest CountingLLL.RevealMachine

theorem CountingLLL.ReciprocalTest.reciprocal_reveal_simulates (ω : Entropy) (n : ℕ) :
    (CountingLLL.RevealMachine.run revealProgram (entropyCode ω) initial n).1 =
      CountingLLL.ReciprocalTest.run ω n := by sorry
