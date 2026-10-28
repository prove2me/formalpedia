-- Prove2me | Theorems.Thm_Erdos261_rep_iff_int
-- name    : Erdos261.rep_iff_int
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:46:48.685565+00:00
-- url     : https://prove2.me/theorems/1134ce7f-a55d-4cd1-bf8b-7d63c37b3d7d
-- title:
--   Integer form of the representation equation $n/2^n=\sum_{k\in S}k/2^k$
-- statement:
--   Write $\operatorname{Rep}$ for a representation $\frac{n}{2^n}=\sum_k \frac{a_k}{2^{a_k}}$ by pairwise distinct positive integers $a_k$ (Erdős Problem 261). **Theorem.** Let $1\le n\le N$ and let $S\subseteq\{1,\dots,N\}$. Put $c_j=j\,[j\in S]-n\,[j=n]$. Then
--
--   $$\frac{n}{2^n}=\sum_{k\in S}\frac{k}{2^k}\iff\sum_{j=1}^{N}c_j\,2^{N-j}=0.$$
--
--   Multiplying by $2^N$ turns the rational identity into an integer column identity, the input of the signed binary-carry formulation.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; Lemma A2 of GPT 6.1 Sol; lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem rep_iff_int (n N : ℕ) (S : Finset ℕ) (hn : 1 ≤ n) (hnN : n ≤ N) (hS : S ⊆ Icc 1 N) :
    (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k ↔
      ∑ j ∈ Icc 1 N, ((if j ∈ S then (j : ℤ) else 0) - (if j = n then (n : ℤ) else 0)) *
        2 ^ (N - j) = 0 := by sorry

end Erdos261
