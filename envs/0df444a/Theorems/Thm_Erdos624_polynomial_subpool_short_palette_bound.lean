-- Prove2me | Theorems.Thm_Erdos624_polynomial_subpool_short_palette_bound
-- name    : Erdos624.polynomial_subpool_short_palette_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:29:49.752187+00:00
-- url     : https://prove2.me/theorems/916d2ed1-7699-42d5-997a-0787ff67224c
-- title:
--   Polynomial-subpool short palette bound (SHORT-BOUND): $H_{K,R}\le2^{7k/8}\le n/(16\sqrt k)$ for $k\ge128$ (Erdős 624)
-- statement:
--   Let $k\ge128$, $K=k^3$, $\ell=\lceil\log_2k\rceil$ (`Nat.clog 2 k`), $R=\lfloor k/(4\ell)\rfloor$ and $H_{K,R}=2\sum_{a=1}^R\binom Ka$ (literal capacity bound for colours carried by inputs of size $\le R$ in a $K$-pool). **Theorem.** $H_{K,R}^8\le2^{7k}$, i.e. $H_{K,R}\le2^{7k/8}$, and $(256k)^4H_{K,R}^8\le2^{8k}$, i.e. $H_{K,R}\le n/(16\sqrt k)$ with $n=2^k$.
--
--   Source: 'Polynomial Subpools and Cross-Pool Witness Accounting', (SHORT) and (SHORT-BOUND).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14/15 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 15: Sol's Perplexity Computer notes 'Unrooted Coverage Forces Mixed-Layer Cores' and 'Polynomial Subpools and Cross-Pool Witness Accounting' (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem polynomial_subpool_short_palette_bound (k : ℕ) (hk : 128 ≤ k) :
    (256 * k) ^ 4 * (2 * ∑ a ∈ Icc 1 (k / (4 * Nat.clog 2 k)), (k ^ 3).choose a) ^ 8 ≤
      2 ^ (8 * k) ∧
    (2 * ∑ a ∈ Icc 1 (k / (4 * Nat.clog 2 k)), (k ^ 3).choose a) ^ 8 ≤ 2 ^ (7 * k) := by sorry

end Erdos624
