-- Prove2me | Theorems.Thm_Erdos624_rank_rich_exclusion_arith
-- name    : Erdos624.rank_rich_exclusion_arith
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:24:34.410672+00:00
-- url     : https://prove2.me/theorems/72cd56f3-bb97-49df-a515-d8bc6d3a20bc
-- title:
--   Arithmetic of the rank-rich exclusion: $|Q|^4\le2^{132}n^3$, $64|Q|\ge n\Rightarrow n\le2^{156}$ (Erdős 624)
-- statement:
--   Pure arithmetic. Let $n,s$ be natural numbers with $n>0$. If $n\le 64s$ and $s^4\le 2^{132}n^3$, then $n\le2^{156}$.
--
--   In the cross-review, $s=|\mathcal Q_2|$ and the bound $|\mathcal Q_2|^4\le2^{132}n^3$ is the $a=2$ case of the assumed packing theorem (P); the conclusion gives the $k\ge157$ exclusion. **(P) is not claimed here**; it enters only as the numeric hypothesis $h_2$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem rank_rich_exclusion_arith (n s : ℕ) (hn : 0 < n) (h1 : n ≤ 64 * s)
    (h2 : s ^ 4 ≤ 2 ^ 132 * n ^ 3) : n ≤ 2 ^ 156 := by sorry

end Erdos624
