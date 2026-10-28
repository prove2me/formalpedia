-- Prove2me | Theorems.Thm_Erdos624_hereditary_deficit_bound
-- name    : Erdos624.hereditary_deficit_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T20:10:34.726754+00:00
-- url     : https://prove2.me/theorems/3214279e-abfb-4eb9-bef0-45cdd3ce9eb3
-- title:
--   Hereditary deficit bound (N*): mean missing colours on $(k-1)$-faces (Erdős 624)
-- statement:
--   Let $C$ be a colour set with $|C|=n=2^k$, $k\ge3$, and $L:\mathcal P(U)\to\mathcal P(C)$ a list map with $|L(A)|\le2$ for every input $A$. For a face $W$ write $J(W)=\bigcup_{A\subseteq W}L(A)$ and $D(W)=n-|J(W)|$ (colours missing on $W$). **Theorem (N*).** For every pool $P\subseteq U$ with $N=|P|\ge k$, $$(N-k)\,n\binom{N}{k-1}\le 12\,(N-k+2)\sum_{W\in\binom P{k-1}}D(W),$$ i.e. $\mathbb E_{W}D(W)\ge\gamma(N,k)\,n$ with $\gamma(N,k)=\frac{N-k}{12(N-k+2)}$. No covering hypothesis is needed.
--
--   Source: 'Simultaneous Outside Coverage and Core Erasure', (N*).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14/15 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 15: Sol's Perplexity Computer notes (outside coverage / core erasure, best dense cores, near-saturation, witness backbone, supported-loss localization, unrooted mixed-layer cores, polynomial subpools) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem hereditary_deficit_bound {U : Type*} [DecidableEq U] {C : Type*} [Fintype C] [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 3 ≤ k) (hC : Fintype.card C = 2 ^ k)
    (hb : ∀ A, #(L A) ≤ 2) (P : Finset U) (hP : k ≤ #P) :
    (#P - k) * 2 ^ k * (#P).choose (k - 1) ≤
      12 * (#P - k + 2) * ∑ W ∈ P.powersetCard (k - 1), (2 ^ k - #(W.powerset.biUnion L)) := by sorry

end Erdos624
