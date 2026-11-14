-- Prove2me | Theorems.Thm_CountingLLL_ReciprocalTest_operational_phase_probabilities
-- name    : CountingLLL.ReciprocalTest.operational_phase_probabilities
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T10:20:25.342479+00:00
-- url     : https://prove2.me/theorems/8eaa44bb-0d19-46a7-b565-bf438e314843
-- title:
--   Operational ReciprocalTest conditional oracle, fair-bit, and uniform probabilities
-- statement:
--   Under the original entropy law with $B\le1$, at any exact operational state: an oracle query returns zero with probability $B$; a Coin fair-bit query returns one with probability $1/2$; and a finite-uniform check selects its distinguished zero value with probability $1/((j-1)+1)$. Each probability is stated as a joint state-and-outcome factorization, so no positive-probability conditioning assumption is needed.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, Algorithm 6, pp. 27–28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ReciprocalEncodedLaw
open MeasureTheory ProbabilityTheory CountingLLL.ReciprocalTest
open scoped ENNReal

theorem CountingLLL.ReciprocalTest.operational_phase_probabilities (B : ℝ≥0∞) (hB : B ≤ 1) (n : ℕ) :
    (∀ (s : State) (k : Context), s.phase = .coinOracle k →
      entropyLaw B {ω | run ω n = s ∧ ω.1 s.oracleUsed = false} =
        entropyLaw B {ω | run ω n = s} * B) ∧
    (∀ (s : State) (k : Context), s.phase = .coinFair k →
      entropyLaw B {ω | run ω n = s ∧ ω.2.1 s.fairUsed = true} =
        entropyLaw B {ω | run ω n = s} * (1/2)) ∧
    (∀ (s : State), s.phase = .uniformCheck →
      entropyLaw B {ω | run ω n = s ∧ (ω.2.2 (s.j-1,s.uniformUsed)).val = 0} =
        entropyLaw B {ω | run ω n = s} * (1/(((s.j-1)+1 : ℕ) : ℝ≥0∞))) := by sorry
