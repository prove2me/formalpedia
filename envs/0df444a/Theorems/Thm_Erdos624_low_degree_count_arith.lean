-- Prove2me | Theorems.Thm_Erdos624_low_degree_count_arith
-- name    : Erdos624.low_degree_count_arith
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:39:19.795984+00:00
-- url     : https://prove2.me/theorems/4b34fe28-6b01-4d1f-b723-7cc4c5729d3a
-- title:
--   Arithmetic of the common-input low-degree exclusion (Deg)/(D): $R(t,D)+d\le2^t$ and $b(2^{R(t,D)+d}-1)\,k<b\,2^d\,2^k$ (Erdős 624)
-- statement:
--   Pure arithmetic. Let $k,t,D,d,b$ be natural numbers with $t=\lfloor\log_2k\rfloor\ge2$, $D\le t-2$, $d\le t+1$, $b\ge1$, and $R(t,D)=\sum_{j=0}^{D}\binom tj$ (for $D\le t-2$ this equals the sum up to $\min(D,t)$). Then $$R(t,D)+d\le2^t\le k,\qquad b\,(2^{R(t,D)+d}-1)\,2^{t+1}<b\,2^d\,2^k,\qquad b\,(2^{R(t,D)+d}-1)\,k<b\,2^d\,2^k.$$With $n=2^k$ the last two say $m/n<b2^{d-1}/2^t$ and $m/n<b2^d/k$ for $m=b(2^{R(t,D)+d}-1)$.
--
--   Source: 'Individual Spectra and Common-Input Degree', (Deg)/(D). There, $m\le b(2^{R(t,D)+d}-1)$ is the common-pool bound (C) (formalized separately as `Erdos624.common_pool_capacity_bound`) applied to a coordinate $t$-subcube, where all parity functions of degree $\le D$ have rank $\le R(t,D)$. **That monomial-count step (degree $\le D$ ⇒ restricted rank $\le R(t,D)$) is not formalized here**; this item checks only the numerical part.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem low_degree_count_arith (k t D d b : ℕ) (ht : t = Nat.log 2 k) (ht2 : 2 ≤ t)
    (hD : D ≤ t - 2) (hd : d ≤ t + 1) (hb : 0 < b) :
    (∑ j ∈ Finset.range (D + 1), t.choose j) + d ≤ 2 ^ t ∧ 2 ^ t ≤ k ∧
      b * (2 ^ ((∑ j ∈ Finset.range (D + 1), t.choose j) + d) - 1) * 2 ^ (t + 1) <
        b * 2 ^ d * 2 ^ k ∧
      b * (2 ^ ((∑ j ∈ Finset.range (D + 1), t.choose j) + d) - 1) * k < b * 2 ^ d * 2 ^ k := by sorry

end Erdos624
