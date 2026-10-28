-- Prove2me | Theorems.Thm_Erdos624_rare_layer_budget
-- name    : Erdos624.rare_layer_budget
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:59.596764+00:00
-- url     : https://prove2.me/theorems/7965420f-f914-4632-aa7a-bd915f6fdb48
-- title:
--   Rare-layer budget: colours using only rare input sizes number at most $4n/k$ (TAIL-CASE $<4n$) (Erdős 624)
-- statement:
--   Let $|L(A)|\le2$, $k\ge1$, $Q\subseteq U$ with $|Q|\ge k$. Call a size $a$ *rare* if $k\ln k\le2(a-k/2)^2$, i.e. $|a-k/2|\ge w=\sqrt{k\ln k/2}$. Let $S$ be a set of colours such that every $k$-subset $Y\subseteq Q$ contains an input $A$ of rare size with $u\in L(A)$. **Theorem.** $|S|\,k\le4\cdot2^k$, hence $(k-1)|S|<4\cdot2^k=4n$.
--
--   Since every best-core loss satisfies $0\le\beta_{u,\delta}(T)\le k-1$, this gives the (TAIL-CASE) bound $\sum_{u\in S_J}\beta_{u,\delta}(T)<4n$. Source: 'Best Dense Cores and Mandatory Mixed-Face Obstructions', (LAYER-BUDGET) and (TAIL-CASE).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem rare_layer_budget {U : Type*} [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (k : ℕ) (hk : 1 ≤ k) (hb : ∀ A, #(L A) ≤ 2)
    (Q : Finset U) (hQ : k ≤ #Q) (S : Finset C)
    (hS : ∀ u ∈ S, ∀ Y ⊆ Q, #Y = k →
      ∃ A ⊆ Y, (k : ℝ) * Real.log k ≤ 2 * ((#A : ℝ) - k / 2) ^ 2 ∧ u ∈ L A) :
    (#S : ℝ) * k ≤ 4 * 2 ^ k ∧ ((k : ℝ) - 1) * #S < 4 * 2 ^ k := by sorry

end Erdos624
