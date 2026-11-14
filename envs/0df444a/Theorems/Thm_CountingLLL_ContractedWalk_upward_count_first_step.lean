-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_upward_count_first_step
-- name    : CountingLLL.ContractedWalk.upward_count_first_step
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:33:15.153511+00:00
-- url     : https://prove2.me/theorems/64ee58b0-a008-4c32-b0df-0997123a3b68
-- title:
--   First-step decomposition of upward count
-- statement:
--   For a contracted-walk path starting above zero whose shifted tail reaches zero, the number of upward moves before absorption equals the indicator that the first step is upward plus the corresponding upward count of the shifted path from its new level. This pathwise identity is a first-step ingredient for the generating-function recursion.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.upward_count_first_step (ω : Tape) (i : ℕ) (hi : 0 < i) (h : ∃ t, level (fun n => ω (n+1)) (if ω 0 then i+2 else i-1) t = 0) : upwardCount ω i = (if ω 0 then 1 else 0) + upwardCount (fun n => ω (n+1)) (if ω 0 then i+2 else i-1) := by sorry
