-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_stopped_change_bound
-- name    : CountingLLL.ContractedWalk.stopped_change_bound
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T08:28:14.208198+00:00
-- url     : https://prove2.me/theorems/0ce3316f-b972-4bfa-837d-b5bd30b7f149
-- title:
--   Contracted walk: number of changes before absorption
-- statement:
--   Consider the absorbed walk with upward steps of two and downward steps of one, started at level $2j-1$ with $j\geq 1$. If it reaches zero, and $N$ is the initial counter $j$ plus the number of upward steps before absorption, then at most $3N$ changes occur before absorption. This is a pathwise bound for the abstract contracted walk, not a coupling with the original algorithm.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC #442, proof of Lemma 6.5, computational overhead, p. 28, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedGF
open CountingLLL.ContractedWalk

theorem CountingLLL.ContractedWalk.stopped_change_bound (ω : Tape) (j : ℕ) (hj : 1 ≤ j) (h : ∃ t, level ω (2*j-1) t = 0) : stopTime ω (2*j-1) ≤ 3 * (j + upwardCount ω (2*j-1)) := by sorry
