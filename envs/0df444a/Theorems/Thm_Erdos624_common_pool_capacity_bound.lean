-- Prove2me | Theorems.Thm_Erdos624_common_pool_capacity_bound
-- name    : Erdos624.common_pool_capacity_bound
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:24:56.552549+00:00
-- url     : https://prove2.me/theorems/75c7b4ac-e161-4390-a186-78fb2445c1ff
-- title:
--   Common-pool low-rank bound (C): $|S|\le b(2^{R+d}-1)$ (Erdős 624)
-- statement:
--   Setting: $U$ is a finite set of inputs, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (the actual colour lists), $k$ a natural number. A colour $u$ is *nonbottom* if $u\notin L(\varnothing)$ and *covering* if every $k$-subset $Y\subseteq U$ contains some $A$ with $u\in L(A)$. An *actual minimal witness* of $u$ is $F\subseteq U$ with $u\in L(F)$ and $u\notin L(F')$ for every $F'\subsetneq F$. A *valid label* for $u$ is a map $p:U\to V$ into an $\mathbb F_2$-vector space with $\sum_{x\in F}p(x)=0$ for every actual minimal witness $F$ with $1\le|F|\le k$. For $T\subseteq U$, $\operatorname{rk}(T)=\dim\operatorname{span}p(T)$ and $\operatorname{rk}(U)=\dim\operatorname{span}p(U)$ (the dimension of the valid parity space). Here each colour $u$ in a set $S$ has its own valid label $p_u:U\to V$ (all labels taking values in one $\mathbb F_2$-space $V$, which loses no generality). **Theorem (C).** Suppose every list has size $|L(A)|\le b$, every $u\in S$ is nonbottom and covering with valid label $p_u$ of global rank $\operatorname{rk}_u(U)\ge k-d$ (stated as $k\le\operatorname{rk}_u(U)+d$), and there is one common pool $P\subseteq U$ with $\operatorname{rk}_u(P)\le R$ for all $u\in S$, where $R+d\le k$ and $R+d\le|P|$. Then $|S|\le b\,(2^{R+d}-1)$.
--
--   Source: 'Individual Spectra and Common-Input Degree', boxed bound (C); it also contains the equal-label capacity bound of 'Coordinate-Label Diversity and Low-Rank Tails' as a special case.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem common_pool_capacity_bound {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (b k d R : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (p : C → U → W) (hu : ∀ u ∈ S, u ∉ L ∅)
    (hcov : ∀ u ∈ S, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (hvalid : ∀ u ∈ S, ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p u x = 0)
    (hglob : ∀ u ∈ S,
      k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p u))) + d)
    (P : Finset U)
    (hpool : ∀ u ∈ S,
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (p u '' (P : Set U))) ≤ R)
    (hRk : R + d ≤ k) (hRP : R + d ≤ #P) :
    #S ≤ b * (2 ^ (R + d) - 1) := by sorry

end Erdos624
