-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_running_level_bound
-- name    : CountingLLL.ContractedWalk.running_level_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:29:36.390336+00:00
-- url     : https://prove2.me/theorems/e0f37061-74be-4221-8527-9aa81fce3737
-- title:
--   Contracted walk: level bounded by the running counter
-- statement:
--   In the abstract contracted walk, start at level $2j-1$ with $j\ge 1$. At any time, let $J$ be the initial counter $j$ plus the number of upward changes so far. Then the current level is at most $2J-1$. This pathwise inequality is part of the source computational-overhead argument; connecting the abstract walk to the operational algorithm remains a separate task.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, computational overhead, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open CountingLLL.ContractedWalk
open scoped BigOperators

theorem CountingLLL.ContractedWalk.running_level_bound (ω : Tape) (j t : ℕ) (hj : 1 ≤ j) : level ω (2*j-1) t ≤ 2 * (j + ∑ k ∈ Finset.range t, if level ω (2*j-1) k ≠ 0 ∧ ω k = true then 1 else 0) - 1 := by sorry
