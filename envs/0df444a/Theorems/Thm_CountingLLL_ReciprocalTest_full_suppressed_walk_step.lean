-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_full_suppressed_walk_step
-- name    : CountingLLL.ReciprocalTest.full_suppressed_walk_step
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:46:46.007031+00:00
-- url     : https://prove2.me/theorems/d37b5ec1-0a91-4976-9a2b-78c4b7119879
-- title:
--   Counter changes of the fully suppressed ReciprocalTest
-- statement:
--   Once the fully suppressed ReciprocalTest has entered its main walk phases, each atomic step remains in those phases and changes the counter pair in one of three ways: no change, a decrease of the first counter by one, or an increase by two and one respectively. This is a pathwise statement for every entropy tape and is the deterministic basis for contracting self-loops in the paper’s walk.
-- source:
--   Liu, Wang, Yin, Zhang, Zhou, A Counting and Sampling Lovász Local Lemma, STOC submission #442, §6.2, Lemma 6.5, PDF p. 28, contracted walk. This is the pathwise transition support, not the transition probabilities.

import Definitions.Def_CountingLLL_ReciprocalAllSuppressed
open CountingLLL.ReciprocalTest

theorem CountingLLL.ReciprocalTest.full_suppressed_walk_step (ω : Entropy) (s : State) (hs : (match s.phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False)) :
    (match (allSuppressedStep ω s).phase with
    | .loop | .coinOracle .first | .coinFair .first | .coinOracle .second | .coinFair .second
    | .uniformCheck | .done _ => True | _ => False) ∧
    (((allSuppressedStep ω s).i = s.i ∧ (allSuppressedStep ω s).j = s.j) ∨
     ((allSuppressedStep ω s).i = s.i - 1 ∧ (allSuppressedStep ω s).j = s.j) ∨
     ((allSuppressedStep ω s).i = s.i + 2 ∧ (allSuppressedStep ω s).j = s.j + 1)) := by sorry
