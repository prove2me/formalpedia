-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_transition_law
-- name    : CountingLLL.ReciprocalTest.operational_transition_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:11:09.756237+00:00
-- url     : https://prove2.me/theorems/1b504bed-a30e-489b-a38b-714abe24c2b0
-- title:
--   Operational query-step transition law
-- statement:
--   For the original ReciprocalTest entropy law, fix a current state $s$ with queried coordinate $a$ and a candidate next state $s'.$ The joint probability of being in $s$ at step $n$ and in $s'$ at step $n+1$ is the state probability times the marginal probability of the queried values which make the deterministic step reach $s'.$ These are one-step laws; eventual return and total expected cost are separate.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest CountingLLL.RevealMachine
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.operational_transition_law (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ)
    (s s' : State) (a : ReadIndex) (ha : readIndex s = some a) :
    entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s ∧ CountingLLL.ReciprocalTest.run ω (n+1) = s'} =
      entropyLaw B {ω | CountingLLL.ReciprocalTest.run ω n = s} *
        readLaw B a {v | step (uniformEntropy v) s = s'} := by sorry
