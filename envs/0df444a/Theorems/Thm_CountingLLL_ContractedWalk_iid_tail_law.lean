-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_iid_tail_law
-- name    : CountingLLL.ContractedWalk.iid_tail_law
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:34:30.025322+00:00
-- url     : https://prove2.me/theorems/c69eeeae-bf6a-4a71-9b99-5f7de2b6ef71
-- title:
--   Contracted walk IID tail has the original law
-- statement:
--   Removing the first bit from an IID contracted-walk increment stream preserves its product law. This is the fixed-time tail-law ingredient for the source’s first-step generating-function analysis.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open MeasureTheory ProbabilityTheory CountingLLL.ContractedWalk
open scoped ENNReal

theorem CountingLLL.ContractedWalk.iid_tail_law (p : ℝ≥0∞) (hp : p ≤ 1) : (tapeLaw p).map (fun ω n => ω (n+1)) = tapeLaw p := by sorry
