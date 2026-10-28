-- Prove2me | Theorems.Thm_Erdos624_even_packet_capacity
-- name    : Erdos624.even_packet_capacity
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:36:34.508975+00:00
-- url     : https://prove2.me/theorems/49d8b09c-0721-4e12-a10a-b6206f6adc8c
-- title:
--   Even-packet capacity: $d+1$ packets whose zero-sum subsets are even packet unions bound the colours by $b(2^d-1)$ (Erdős 624)
-- statement:
--   Setting: $U$ is a finite set of inputs, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (the actual colour lists), $k$ a natural number. A colour $u$ is *nonbottom* if $u\notin L(\varnothing)$ and *covering* if every $k$-subset $Y\subseteq U$ contains some $A$ with $u\in L(A)$. An *actual minimal witness* of $u$ is $F\subseteq U$ with $u\in L(F)$ and $u\notin L(F')$ for every $F'\subsetneq F$. A *valid label* for $u$ is a map $p:U\to V$ into an $\mathbb F_2$-vector space with $\sum_{x\in F}p(x)=0$ for every actual minimal witness $F$ with $1\le|F|\le k$. For $T\subseteq U$, $\operatorname{rk}(T)=\dim\operatorname{span}p(T)$ and $\operatorname{rk}(U)=\dim\operatorname{span}p(U)$ (the dimension of the valid parity space). Each colour $u\in S$ has its own valid label $p_u$ into one $\mathbb F_2$-space. **Theorem.** Assume $|L(A)|\le b$, every $u\in S$ is nonbottom and covering with $\operatorname{rk}_u(U)\ge k-d$ (stated as $k\le\operatorname{rk}_u(U)+d$). Let $P_0,\dots,P_d$ be pairwise disjoint nonempty packets with $|P_0\cup\dots\cup P_d|\le k$ such that for every $u\in S$: $\sum_{P_0\cup P_j}p_u=0$ for $j\ne0$, and every zero-sum $G\subseteq\bigcup_jP_j$ is a union of an even number of packets. Then $|S|\le b(2^d-1)$.
--
--   This is the **deterministic capacity core** of Sol's 'Bias-Free Colour Bounds' (and of 'Bias-Free Bounds on Colour-Dependent Dense Pools'): there, packets with these properties are constructed probabilistically for $s=b(2^d-1)+1$ colours, which this theorem shows is impossible. The probabilistic construction is not formalized.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem even_packet_capacity {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (b k d : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (p : C → U → W) (hu : ∀ u ∈ S, u ∉ L ∅)
    (hcov : ∀ u ∈ S, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (hvalid : ∀ u ∈ S, ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p u x = 0)
    (hglob : ∀ u ∈ S,
      k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p u))) + d)
    (P : Fin (d + 1) → Finset U) (hdisj : ∀ j l, j ≠ l → Disjoint (P j) (P l))
    (hne : ∀ j, (P j).Nonempty) (hk : #(Finset.univ.biUnion P) ≤ k)
    (hpair : ∀ u ∈ S, ∀ j, j ≠ 0 → ∑ x ∈ P 0 ∪ P j, p u x = 0)
    (hzs : ∀ u ∈ S, ∀ G ⊆ Finset.univ.biUnion P, ∑ x ∈ G, p u x = 0 →
      ∃ I : Finset (Fin (d + 1)), Even #I ∧ G = I.biUnion P) :
    #S ≤ b * (2 ^ d - 1) := by sorry

end Erdos624
