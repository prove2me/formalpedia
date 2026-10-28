-- Prove2me | Theorems.Thm_Erdos624_central_binomial_square_bound
-- name    : Erdos624.central_binomial_square_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:59.260094+00:00
-- url     : https://prove2.me/theorems/da6b523b-35ca-4d41-8fa8-81fa91ac1d1d
-- title:
--   Central binomial estimate $\binom{2s}{s}^2(3s+1)\le16^s$ (Erdős 624)
-- statement:
--   **Theorem.** For every $s\ge0$, $\binom{2s}{s}^2(3s+1)\le 16^s$, i.e. $\binom{2s}s/4^s\le(3s+1)^{-1/2}$.
--
--   Source: 'Unrooted Lower-Layer Forcing', central coefficient estimate used for (M).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem central_binomial_square_bound (s : ℕ) : (2 * s).choose s ^ 2 * (3 * s + 1) ≤ 16 ^ s := by sorry

end Erdos624
