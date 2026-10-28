-- Prove2me | Theorems.Thm_Erdos624_top_layer_free_packing
-- name    : Erdos624.top_layer_free_packing
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:34:25.546004+00:00
-- url     : https://prove2.me/theorems/a4ae9ab4-bc6f-44df-9c5a-12dad37c86fa
-- title:
--   Top-layer-free packing (29): $n/64$ colours with $256k(k-1)|\mathcal P_u(w)|>N$ for every form $w$ (Erdős 624)
-- statement:
--   Throughout, $U$ is a finite set of inputs, $C$ a finite set of colours with $|C|=n=2^k$, and $g_0,g_1:\mathcal P(U)\to C$ two arbitrary maps; $L(A)=\{g_0(A),g_1(A)\}$. Here $|U|=n$. The *proper minimal witnesses* of a colour $u$ inside $W$ are the $A\subseteq W$ with $0<|A|<k$, $u\in L(A)$ and $u\notin L(B)$ for all $B\subsetneq A$; a *certificate* is $w:U\to\mathbf F_2$ with $\sum_{x\in A}w(x)=1$ on every such $A$. **Theorem.** Let $k\ge3$, $V\subseteq U$ with $N=|V|\ge2^{28}k^4$, and suppose the pair covers every $k$-subset of $V$. Then there is a set $H$ of colours with $64|H|\ge n$, all outside $L(\varnothing)$, such that for every $u\in H$ and **every** form $w:U\to\mathbf F_2$ (chosen independently per colour) there is a family $\mathcal P$ of pairwise disjoint proper minimal witnesses $A\subseteq V$ of $u$, each with $\sum_{x\in A}w(x)=0$, and $N<256k(k-1)|\mathcal P|$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem top_layer_free_packing {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (hC : Fintype.card C = 2 ^ k) (g0 g1 : Finset U → C) (V : Finset U)
    (hV : 2 ^ 28 * k ^ 4 ≤ #V)
    (hcov : ∀ Y ∈ powersetCard k V, ∀ u : C, ∃ A ⊆ Y, u ∈ ({g0 A, g1 A} : Finset C)) :
    ∃ H : Finset C, 2 ^ k ≤ 64 * #H ∧ ∀ u ∈ H, u ∉ ({g0 ∅, g1 ∅} : Finset C) ∧
      ∀ w : U → ZMod 2, ∃ P : Finset (Finset U),
        (∀ A ∈ P, A ⊆ V ∧ 0 < #A ∧ #A < k ∧ u ∈ ({g0 A, g1 A} : Finset C) ∧
          (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) ∧ ∑ x ∈ A, w x = 0) ∧
        (∀ A ∈ P, ∀ B ∈ P, A ≠ B → Disjoint A B) ∧
        #V < 256 * k * (k - 1) * #P := by sorry

end Erdos624
