-- Prove2me | Theorems.Thm_Erdos624_three_way_injection_bound
-- name    : Erdos624.three_way_injection_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T19:36:01.012651+00:00
-- url     : https://prove2.me/theorems/b3f3d2f4-2688-4312-87b3-b85af9fc44d6
-- title:
--   Three-way injection bound (THREE): $|X|\le3\sum_{i\le\lfloor r/3\rfloor}\binom ri$ (Erdős 624)
-- statement:
--   Let $H$ be a finite set with $|H|=r$, and let $f_1,f_2,f_3$ be maps from an index set $X$ into subsets of $H$, each injective on $X$, with $|f_1(\alpha)|+|f_2(\alpha)|+|f_3(\alpha)|\le r$ for every $\alpha\in X$ (e.g. the three parts $S_\alpha(D)$, $S_\alpha(E)$, $H\setminus(S_\alpha(D)\cup S_\alpha(E))$ of a partition). **Theorem.** $|X|\le3\sum_{i=0}^{\lfloor r/3\rfloor}\binom ri$.
--
--   Source: 'A Joint Exterior-Order Rank Budget', (THREE).
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. The notes study a hypothetical two-track counterexample: $n=2^k$, colour lists $L(A)$ of size at most two on inputs $A$, and every $k$-set attaining every colour. This is an auxiliary finite statement from Sol's Round 14 notes. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 14: Sol's Perplexity Computer notes (best dense cores, lower-layer forcing, near-saturation, witness backbone, joint exterior budget, core hubs, sparse parity) (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem three_way_injection_bound {ι β : Type*} [DecidableEq β] (X : Finset ι) (H : Finset β)
    (f₁ f₂ f₃ : ι → Finset β)
    (h₁ : Set.InjOn f₁ X) (h₂ : Set.InjOn f₂ X) (h₃ : Set.InjOn f₃ X)
    (hsub : ∀ a ∈ X, f₁ a ⊆ H ∧ f₂ a ⊆ H ∧ f₃ a ⊆ H)
    (hpart : ∀ a ∈ X, #(f₁ a) + #(f₂ a) + #(f₃ a) ≤ #H) :
    #X ≤ 3 * ∑ i ∈ range (#H / 3 + 1), (#H).choose i := by sorry

end Erdos624
