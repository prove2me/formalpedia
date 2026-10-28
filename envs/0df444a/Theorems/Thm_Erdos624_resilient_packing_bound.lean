-- Prove2me | Theorems.Thm_Erdos624_resilient_packing_bound
-- name    : Erdos624.resilient_packing_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:34:26.355148+00:00
-- url     : https://prove2.me/theorems/d502ebbc-eb0c-4cf3-94e1-bb465f761428
-- title:
--   Resilience forces large disjoint packings of violating proper witnesses: $256k(k-1)|\mathcal P|>N$ (29) (Erdős 624)
-- statement:
--   Let $U$ be a finite set, $C$ a finite set of colours, $g_0,g_1:\mathcal P(U)\to C$, $L(A)=\{g_0(A),g_1(A)\}$, $V\subseteq U$ with $N=|V|$, $k\in\mathbb N$ and $u\in C$. The *proper minimal witnesses* of a colour $u$ inside $W$ are the $A\subseteq W$ with $0<|A|<k$, $u\in L(A)$ and $u\notin L(B)$ for all $B\subsetneq A$; a *certificate* is $w:U\to\mathbf F_2$ with $\sum_{x\in A}w(x)=1$ on every such $A$. Assume $u$ is resilient: for every $R\subseteq V$ with $256k|R|\le N$, the proper minimal witnesses of $u$ in $V\setminus R$ admit no certificate. Then for **every** form $w:U\to\mathbf F_2$ there is a family $\mathcal P$ of pairwise disjoint proper minimal witnesses $A\subseteq V$ of $u$ with $\sum_{x\in A}w(x)=0$ and $$N<256k(k-1)|\mathcal P|.\qquad(29)$$(Here $k-1$ is truncated natural-number subtraction; no lower bound on $k$ is needed.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem resilient_packing_bound {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (g0 g1 : Finset U → C) (V : Finset U) (u : C)
    (hres : ∀ R ⊆ V, 256 * k * #R ≤ #V → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1)
    (w : U → ZMod 2) :
    ∃ P : Finset (Finset U),
      (∀ A ∈ P, A ⊆ V ∧ 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
        (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0) ∧
      (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
      #V < 256 * k * (k - 1) * #P := by sorry

end Erdos624
