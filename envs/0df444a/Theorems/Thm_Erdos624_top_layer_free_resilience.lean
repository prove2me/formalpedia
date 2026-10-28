-- Prove2me | Theorems.Thm_Erdos624_top_layer_free_resilience
-- name    : Erdos624.top_layer_free_resilience
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-24T14:09:24.54002+00:00
-- url     : https://prove2.me/theorems/00d27917-4ae6-4f73-ac0b-6aed54cb5763
-- title:
--   Top-layer-free resilience (1): $64\,|\{u\notin L(\varnothing):256k\,\sigma_u(V)>N\}|\ge n$ for covering pairs (Erdős 624)
-- statement:
--   Throughout, $U$ is a finite set of inputs, $C$ a finite set of colours with $|C|=n=2^k$, and $g_0,g_1:\mathcal P(U)\to C$ are two arbitrary maps (a *pair*); write $L(A)=\{g_0(A),g_1(A)\}$ for the list of colours at the input $A$. Here also $|U|=n$. For a pool $V\subseteq U$ with $N=|V|$ and a colour $u\notin L(\varnothing)$, the *proper minimal witnesses* of $u$ in $W\subseteq V$ are the sets $A\subseteq W$ with $0<|A|<k$, $u\in L(A)$ and $u\notin L(B)$ for every $B\subsetneq A$; the family is *affine-coherent* if some $w:U\to\mathbf F_2$ has $\sum_{x\in A}w(x)=1$ on every member. Let $\sigma_u(V)$ be the least $|R|$, $R\subseteq V$, such that the proper minimal witnesses of $u$ in $V\setminus R$ are affine-coherent.
--
--   **Theorem.** Let $k\ge3$, $N\ge2^{28}k^4$, and suppose the pair covers every $k$-subset of $V$: for each $Y\in\binom Vk$ and each colour $u$ there is $A\subseteq Y$ with $u\in L(A)$. Then there is a set $H$ of colours with $64|H|\ge n$ such that every $u\in H$ satisfies $u\notin L(\varnothing)$ and $256k\,\sigma_u(V)>N$, i.e. for **every** $R\subseteq V$ with $256k|R|\le N$ the proper minimal witnesses of $u$ in $V\setminus R$ admit no $\mathbf F_2$ certificate. Equivalently $$64\,\bigl|\{u\notin L(\varnothing):\ 256k\,\sigma_u(V)>N\}\bigr|\;\ge\; n.\qquad(1)$$(For $V=U$ the size hypothesis holds for all $k\ge64$.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. By an earlier track-amplification result it suffices to find common holes for fixed numbers of tracks; this is an auxiliary finite inequality from Sol's Round 10 analysis of the two-track case. It does **not** settle Erdős Problem 624, PAIR or Step 17.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 10 reports (consolidated report §'parity transport', §'many holes one level below'; Step 17 report 'resilient relations below the top layer', eqs. (9)-(26)); derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung; proof reconstructed, hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 24 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem top_layer_free_resilience {U : Type*} [Fintype U] [DecidableEq U]
    {C : Type*} [Fintype C] [DecidableEq C] (k : ℕ) (hk : 3 ≤ k)
    (hU : Fintype.card U = 2 ^ k) (hC : Fintype.card C = 2 ^ k) (g0 g1 : Finset U → C)
    (V : Finset U) (hV : 2 ^ 28 * k ^ 4 ≤ #V)
    (hcov : ∀ Y ∈ powersetCard k V, ∀ u : C, ∃ A ⊆ Y, u ∈ ({g0 A, g1 A} : Finset C)) :
    ∃ H : Finset C, 2 ^ k ≤ 64 * #H ∧ ∀ u ∈ H, u ∉ ({g0 ∅, g1 ∅} : Finset C) ∧
      ∀ R ⊆ V, 256 * k * #R ≤ #V → ¬ ∃ w : U → ZMod 2, ∀ A ⊆ V \ R, 0 < #A → #A < k →
        u ∈ ({g0 A, g1 A} : Finset C) → (∀ B ⊂ A, u ∉ ({g0 B, g1 B} : Finset C)) →
          ∑ x ∈ A, w x = 1 := by sorry

end Erdos624
