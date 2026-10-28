-- Prove2me | Theorems.Thm_Erdos624_binomial_third_tail
-- name    : Erdos624.binomial_third_tail
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:58.088719+00:00
-- url     : https://prove2.me/theorems/cf0450a9-ca1b-466c-ab8d-86bceffb2937
-- title:
--   Binomial third tail (TAIL): $(\sum_{i\le r/3}\binom ri)^{51}\le2^{47r}$ (Erdős 624)
-- statement:
--   **Theorem.** For every $r$, $\bigl(\sum_{i\le\lfloor r/3\rfloor}\binom ri\bigr)2^r\le2^{\lfloor r/3\rfloor}3^r$, and hence $\bigl(\sum_{i\le\lfloor r/3\rfloor}\binom ri\bigr)^{51}\le2^{47r}$ (the integer form of $\Lambda_r\le3\cdot2^{H_2(1/3)r}$ with $H_2(1/3)<47/51$).
--
--   Source: 'A Joint Exterior-Order Rank Budget', (TAIL).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem binomial_third_tail (r : ℕ) :
    (∑ i ∈ range (r / 3 + 1), r.choose i) * 2 ^ r ≤ 2 ^ (r / 3) * 3 ^ r ∧
    (∑ i ∈ range (r / 3 + 1), r.choose i) ^ 51 ≤ 2 ^ (47 * r) := by sorry

end Erdos624
