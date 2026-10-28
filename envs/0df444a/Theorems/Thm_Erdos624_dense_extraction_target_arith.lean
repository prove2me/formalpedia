-- Prove2me | Theorems.Thm_Erdos624_dense_extraction_target_arith
-- name    : Erdos624.dense_extraction_target_arith
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:24:32.090499+00:00
-- url     : https://prove2.me/theorems/99e3159f-0bdd-4f6f-a665-4c3610e6e658
-- title:
--   Arithmetic of the dense-extraction target: $n\le b|S|$, $|S|^4\le2^{104}a^{28}n^3\Rightarrow n\le2^{104}a^{28}b^4$ (Erdős 624)
-- statement:
--   Pure arithmetic. Let $a,b,n,s$ be natural numbers with $n>0$. If $n\le b\,s$ and $s^4\le 2^{104}a^{28}n^3$, then $n\le 2^{104}a^{28}b^4$.
--
--   In the cross-review this is the step showing that the (unproved) dense-pool short-circuit extraction target, combined with the packing theorem (P) $|S|^4\le2^{104}a^{28}n^3$, would bound $n$. **Neither (P) nor the extraction target is claimed here**; both enter only as hypotheses $h_1,h_2$ about numbers.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem dense_extraction_target_arith (a b n s : ℕ) (hn : 0 < n) (h1 : n ≤ b * s)
    (h2 : s ^ 4 ≤ 2 ^ 104 * a ^ 28 * n ^ 3) : n ≤ 2 ^ 104 * a ^ 28 * b ^ 4 := by sorry

end Erdos624
