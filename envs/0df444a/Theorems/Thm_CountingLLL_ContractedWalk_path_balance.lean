-- Prove2me | Theorems.Thm_CountingLLL_ContractedWalk_path_balance
-- name    : CountingLLL.ContractedWalk.path_balance
-- status  : Proved
-- author  : @wcysai
-- created : 2026-11-13T07:22:28.06853+00:00
-- url     : https://prove2.me/theorems/d3b45416-c066-4913-8607-8a61bb205aba
-- title:
--   Contracted walk pathwise balance
-- statement:
--   For every finite path of the absorbed contracted walk, the current level plus the number of active changes equals the initial level plus three times the number of upward changes. This pathwise conservation identity supports the negative-drift bound.
-- source:
--   Liu, Wang, Yin, Zhang and Zhou, A Counting and Sampling Lovász Local Lemma, STOC 2027 #442, proof of Lemma 6.5, PDF p. 27, https://github.com/sigact-stoc/stoc2027/releases/download/papers-1/442.pdf

import Definitions.Def_CountingLLL_ContractedWalk
open CountingLLL.ContractedWalk
open scoped BigOperators

theorem CountingLLL.ContractedWalk.path_balance (ω : Tape) (i t : ℕ) :
    level ω i t + (∑ k ∈ Finset.range t, if level ω i k = 0 then 0 else 1) =
      i + 3*(∑ k ∈ Finset.range t, if level ω i k ≠ 0 ∧ ω k = true then 1 else 0) := by sorry
