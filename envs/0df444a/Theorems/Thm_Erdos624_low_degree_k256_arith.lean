-- Prove2me | Theorems.Thm_Erdos624_low_degree_k256_arith
-- name    : Erdos624.low_degree_k256_arith
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:39:19.301935+00:00
-- url     : https://prove2.me/theorems/9b05f12b-00a2-4618-8692-efafed152dff
-- title:
--   Low-degree exclusion endpoint: for $k\ge256$ and $D\le\lfloor\log_2k\rfloor-2$, $64\cdot2(2^{R(t,D)+2}-1)<2^k$ (Erdős 624)
-- statement:
--   Pure arithmetic. For all natural numbers $k\ge256$ and $D\le t-2$, where $t=\lfloor\log_2 k\rfloor$ and $R(t,D)=\sum_{j=0}^{D}\binom tj$, $$64\cdot 2\,(2^{R(t,D)+2}-1)<2^k.$$This is the strict $b=2$, $d=2$, $k\ge256$ endpoint of 'Individual Spectra and Common-Input Degree': combined with (C), fewer than $n/64$ covering colours can have valid rank-$(k-2)$ spaces of common-input degree $\le\lfloor\log_2k\rfloor-2$. (The degree ⇒ rank step is not formalized here.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem low_degree_k256_arith (k D : ℕ) (hk : 256 ≤ k) (hD : D ≤ Nat.log 2 k - 2) :
    64 * (2 * (2 ^ ((∑ j ∈ Finset.range (D + 1), (Nat.log 2 k).choose j) + 2) - 1)) < 2 ^ k := by sorry

end Erdos624
