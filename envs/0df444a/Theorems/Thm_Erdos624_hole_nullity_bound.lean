-- Prove2me | Theorems.Thm_Erdos624_hole_nullity_bound
-- name    : Erdos624.hole_nullity_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:29:29.190242+00:00
-- url     : https://prove2.me/theorems/f859c2f9-43e3-4f7f-bfd5-056518e853bf
-- title:
--   Hole nullity bound: a genuine $u$-hole $H$ with $|H|\le k$ has $|H|<\operatorname{rk}(H)+d$ (Erdős 624)
-- statement:
--   Setting: $U$ is a finite set of inputs, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (the actual colour lists), $k$ a natural number. A colour $u$ is *nonbottom* if $u\notin L(\varnothing)$ and *covering* if every $k$-subset $Y\subseteq U$ contains some $A$ with $u\in L(A)$. An *actual minimal witness* of $u$ is $F\subseteq U$ with $u\in L(F)$ and $u\notin L(F')$ for every $F'\subsetneq F$. A *valid label* for $u$ is a map $p:U\to V$ into an $\mathbb F_2$-vector space with $\sum_{x\in F}p(x)=0$ for every actual minimal witness $F$ with $1\le|F|\le k$. For $T\subseteq U$, $\operatorname{rk}(T)=\dim\operatorname{span}p(T)$ and $\operatorname{rk}(U)=\dim\operatorname{span}p(U)$ (the dimension of the valid parity space). **Theorem.** Let $u$ be nonbottom and covering with valid label $p$ of global rank $\operatorname{rk}(U)\ge k-d$ (stated as $k\le\operatorname{rk}(U)+d$). If $H\subseteq U$, $|H|\le k$, is a genuine hole ($u\notin L(A)$ for all $A\subseteq H$), then $|H|<\operatorname{rk}(H)+d$, i.e. the label nullity $\eta(H)=|H|-\operatorname{rk}(H)$ is at most $d-1$.
--
--   Source: 'Actual Witness Spans and Intrinsic Kernel Diversity', exact-size hole extension.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem hole_nullity_bound {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (k d : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + d)
    (H : Finset U) (hH : #H ≤ k) (hhole : ∀ A ⊆ H, u ∉ L A) :
    #H < Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p '' (H : Set U))) + d := by sorry

end Erdos624
