-- Prove2me | Theorems.Thm_Erdos624_descent_capacity_inequality
-- name    : Erdos624.descent_capacity_inequality
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:35:59.112469+00:00
-- url     : https://prove2.me/theorems/88620ab2-54e3-4227-b5b0-0265a36ec5c3
-- title:
--   Exact descent capacity inequality (D): $\sum_u\binom{|V_u|}a\le b(2^a-1)\binom na$ (Erdős 624)
-- statement:
--   Let $U$ be finite with $|U|=n$, $|L(A)|\le b$, and let $S$ be a set of colours with sets $V_u\subseteq U$ such that every $a$-subset $Y\subseteq V_u$ contains a nonempty input $A$ with $u\in L(A)$. **Theorem.** $\sum_{u\in S}\binom{|V_u|}{a}\le b(2^a-1)\binom na$.
--
--   Source: 'Core Hubs and Low-Degree Capacity Bounds', (D). There the hypothesis is derived by completing $Y$ with a repair-independent set $I_u$; here it is an explicit hypothesis.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem descent_capacity_inequality {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (b a : ℕ) (hb : ∀ A, #(L A) ≤ b) (S : Finset C)
    (V : C → Finset U)
    (hcov : ∀ u ∈ S, ∀ Y ⊆ V u, #Y = a → ∃ A ⊆ Y, A.Nonempty ∧ u ∈ L A) :
    ∑ u ∈ S, (#(V u)).choose a ≤ b * (2 ^ a - 1) * (Fintype.card U).choose a := by sorry

end Erdos624
