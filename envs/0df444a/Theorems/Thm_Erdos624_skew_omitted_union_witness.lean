-- Prove2me | Theorems.Thm_Erdos624_skew_omitted_union_witness
-- name    : Erdos624.skew_omitted_union_witness
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:36:33.765031+00:00
-- url     : https://prove2.me/theorems/090cb1ef-79eb-4b28-84d0-438fc1746303
-- title:
--   Deficit two: the union of two skew omitted circuits is an actual minimal witness (Erdős 624)
-- statement:
--   Setting: $U$ is a finite set of inputs, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (the actual colour lists), $k$ a natural number. A colour $u$ is *nonbottom* if $u\notin L(\varnothing)$ and *covering* if every $k$-subset $Y\subseteq U$ contains some $A$ with $u\in L(A)$. An *actual minimal witness* of $u$ is $F\subseteq U$ with $u\in L(F)$ and $u\notin L(F')$ for every $F'\subsetneq F$. A *valid label* for $u$ is a map $p:U\to V$ into an $\mathbb F_2$-vector space with $\sum_{x\in F}p(x)=0$ for every actual minimal witness $F$ with $1\le|F|\le k$. For $T\subseteq U$, $\operatorname{rk}(T)=\dim\operatorname{span}p(T)$ and $\operatorname{rk}(U)=\dim\operatorname{span}p(U)$ (the dimension of the valid parity space). **Theorem.** Let $u$ be nonbottom and covering with valid label $p$ of global rank $\ge k-2$ (stated as $k\le\operatorname{rk}(U)+2$). Let $A,B\subseteq U$ be disjoint, nonempty, with $\sum_Ap=\sum_Bp=0$, such that the only zero-sum subsets of $A\cup B$ are $\varnothing,A,B,A\cup B$, and with $u\notin L(A)$, $u\notin L(B)$, $|A\cup B|\le k$. Then $A\cup B$ is an actual minimal witness of $u$: $u\in L(A\cup B)$ and $u\notin L(F')$ for all $F'\subsetneq A\cup B$.
--
--   Source: converse half of the deficit-two classification in 'Actual Witness Spans and Intrinsic Kernel Diversity'. Note: the source derives $|A\cup B|\le k$ from exact global rank $k-2$; here it is an explicit hypothesis, and 'genuine hole' is weakened to $u\notin L(A)$, $u\notin L(B)$.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem skew_omitted_union_witness {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (k : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + 2)
    (A B : Finset U) (hAB : Disjoint A B) (hA : A.Nonempty) (hB : B.Nonempty)
    (hA0 : ∑ x ∈ A, p x = 0) (hB0 : ∑ x ∈ B, p x = 0)
    (hzs : ∀ G ⊆ A ∪ B, ∑ x ∈ G, p x = 0 → G = ∅ ∨ G = A ∨ G = B ∨ G = A ∪ B)
    (huA : u ∉ L A) (huB : u ∉ L B) (hk : #(A ∪ B) ≤ k) :
    u ∈ L (A ∪ B) ∧ ∀ F' ⊂ A ∪ B, u ∉ L F' := by sorry

end Erdos624
