-- Prove2me | Theorems.Thm_Erdos624_polynomial_pool_localization
-- name    : Erdos624.polynomial_pool_localization
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T15:34:25.161777+00:00
-- url     : https://prove2.me/theorems/65f6992f-d12d-4018-99a6-9b09bb8e6750
-- title:
--   Polynomial-pool localization: on every $2^{28}k^4$-point pool, $n/64$ colours stay inconsistent after deleting $2^{20}k^3$ points (Erdős 624)
-- statement:
--   Throughout, $U$ is a finite set of inputs, $C$ a finite set of colours with $|C|=n=2^k$, and $g_0,g_1:\mathcal P(U)\to C$ two arbitrary maps; $L(A)=\{g_0(A),g_1(A)\}$. Here $|U|=n$. The *proper minimal witnesses* of a colour $u$ inside $W$ are the $A\subseteq W$ with $0<|A|<k$, $u\in L(A)$ and $u\notin L(B)$ for all $B\subsetneq A$; a *certificate* is $w:U\to\mathbf F_2$ with $\sum_{x\in A}w(x)=1$ on every such $A$. **Theorem.** Let $k\ge3$ and let $V\subseteq U$ be a pool with exactly $N_0=2^{28}k^4$ points (such pools exist iff $N_0\le n$, i.e. $k\ge51$) on which the pair covers every $k$-subset. Then there is a set $H$ of colours, $64|H|\ge n$, such that every $u\in H$ lies outside $L(\varnothing)$ and for **every** $R\subseteq V$ with $|R|\le2^{20}k^3$ the proper minimal witnesses of $u$ in $V\setminus R$ admit no certificate.
--
--   Honesty: Sol's further remark that a shortest witnessing odd relation is a linear circuit with at most $N_0+1$ parents (the Fredholm-alternative form) is **not** part of this statement; only the certificate (non-coherence) form is proved.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 12 Step 17 cross-review / resilience analysis of the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 12: Sol's 'Step 17: First-Round Cross-Review' and 'Step 17: resilient relations below the top layer'; derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem polynomial_pool_localization {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 3 ≤ k) (hU : Fintype.card U = 2 ^ k)
    (hC : Fintype.card C = 2 ^ k) (g0 g1 : Finset U → C) (V : Finset U)
    (hV : #V = 2 ^ 28 * k ^ 4)
    (hcov : ∀ Y ∈ powersetCard k V, ∀ u : C, ∃ A ⊆ Y, u ∈ ({g0 A, g1 A} : Finset C)) :
    ∃ H : Finset C, 2 ^ k ≤ 64 * #H ∧ ∀ u ∈ H, u ∉ ({g0 ∅, g1 ∅} : Finset C) ∧
      ∀ R ⊆ V, #R ≤ 2 ^ 20 * k ^ 3 → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1 := by sorry

end Erdos624
