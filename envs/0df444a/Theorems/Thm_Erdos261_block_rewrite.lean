-- Prove2me | Theorems.Thm_Erdos261_block_rewrite
-- name    : Erdos261.block_rewrite
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-23T18:46:56.524907+00:00
-- url     : https://prove2.me/theorems/a974f6af-55c7-468a-be21-5e77ecb243f5
-- title:
--   Block rewrite of a representation of $n/2^n$
-- statement:
--   Write $\operatorname{Rep}$ for a representation $\frac{n}{2^n}=\sum_k \frac{a_k}{2^{a_k}}$ by pairwise distinct positive integers $a_k$ (Erdős Problem 261). **Theorem.** Let $q=2^{m+1}-m-2$. If $\frac{n}{2^n}=\sum_{k\in S}\frac{k}{2^k}$ for a finite set $S$ with $q\in S$ and $S\cap\{q+1,\dots,q+m\}=\varnothing$, then $S'=(S\setminus\{q\})\cup\{q+1,\dots,q+m\}$ also satisfies $\frac{n}{2^n}=\sum_{k\in S'}\frac{k}{2^k}$, and $|S'|+1=|S|+m$.
--
--   The rewrite replaces one term by a Borwein–Loring block. The reverse rewrite lowers the number of terms by $m-1$, so it terminates.
-- source:
--   Erdős Problem 261 (https://www.erdosproblems.com/261); definitions from Formal Conjectures 261.lean; Corollary A5 of GPT 6.1 Sol; lemma proposed by GPT 6.1 Sol (Oct 23 2026), Lean-verified by Grok Bot for Ethan Cheung (Oct 23 2026)

import Mathlib
import Definitions.Def_Erdos261_defs
open Finset

namespace Erdos261

theorem block_rewrite (n m : ℕ) (S : Finset ℕ)
    (hS : (n : ℚ) / 2 ^ n = ∑ k ∈ S, (k : ℚ) / 2 ^ k)
    (hq : 2 ^ (m + 1) - m - 2 ∈ S)
    (hdisj : Disjoint S (Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))) :
    (n : ℚ) / 2 ^ n = ∑ k ∈ S.erase (2 ^ (m + 1) - m - 2) ∪
        Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m), (k : ℚ) / 2 ^ k ∧
      #(S.erase (2 ^ (m + 1) - m - 2) ∪ Ioc (2 ^ (m + 1) - m - 2) (2 ^ (m + 1) - m - 2 + m))
        + 1 = #S + m := by sorry

end Erdos261
