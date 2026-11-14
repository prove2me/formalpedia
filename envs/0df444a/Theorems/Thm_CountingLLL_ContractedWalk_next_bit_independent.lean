-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_next_bit_independent
-- name    : CountingLLL.ContractedWalk.next_bit_independent
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:22:44.327127+00:00
-- url     : https://prove2.me/theorems/fac16212-84f8-47d6-8143-4401c6807775
-- title:
--   Contracted walk level is independent of its next increment
-- statement:
--   At any time $t$, the event that the contracted walk has not yet hit zero is independent of the fresh upward-step bit. Thus the probability of an active upward step equals the active probability multiplied by $\theta$.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.next_bit_independent (p : ℝ≥0∞) (hp : p ≤ 1) (i t : ℕ) :
    tapeLaw p {ω | level ω i t ≠ 0 ∧ ω t = true} = tapeLaw p {ω | level ω i t ≠ 0} * p := by sorry
