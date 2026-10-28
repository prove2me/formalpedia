-- Prove2me | Theorems.Thm_Erdos624_seventeen_packet_contradiction
-- name    : Erdos624.seventeen_packet_contradiction
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:36:33.92698+00:00
-- url     : https://prove2.me/theorems/fb5f87b6-e929-4d2c-9072-9b319e16e7c9
-- title:
--   Seventeen-packet obstruction: three rank-$(k-2)$ colours cannot see 17 packets with exact pair-union kernels at capacity 2 (Erdős 624)
-- statement:
--   Setting: $U$ is a finite set of inputs, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (the actual colour lists), $k$ a natural number. A colour $u$ is *nonbottom* if $u\notin L(\varnothing)$ and *covering* if every $k$-subset $Y\subseteq U$ contains some $A$ with $u\in L(A)$. An *actual minimal witness* of $u$ is $F\subseteq U$ with $u\in L(F)$ and $u\notin L(F')$ for every $F'\subsetneq F$. A *valid label* for $u$ is a map $p:U\to V$ into an $\mathbb F_2$-vector space with $\sum_{x\in F}p(x)=0$ for every actual minimal witness $F$ with $1\le|F|\le k$. For $T\subseteq U$, $\operatorname{rk}(T)=\dim\operatorname{span}p(T)$ and $\operatorname{rk}(U)=\dim\operatorname{span}p(U)$ (the dimension of the valid parity space). **Theorem.** Assume $|L(A)|\le2$ for all $A$. Let $c_1,c_2,c_3$ be three distinct nonbottom covering colours with valid labels $p_1,p_2,p_3$ of global rank $\ge k-2$ (stated as $k\le\operatorname{rk}_i(U)+2$). There do **not** exist 17 pairwise disjoint nonempty packets $P_1,\dots,P_{17}\subseteq U$ such that for all colours $i$ and distinct $j,\ell,m$: $|P_j\cup P_\ell\cup P_m|\le k$; $\sum_{x\in P_j\cup P_\ell}p_i(x)=0$; and every $G\subseteq P_j\cup P_\ell\cup P_m$ with $\sum_{x\in G}p_i(x)=0$ is $\varnothing$ or one of the three pair unions (together: the kernel condition (K) $\ker(p_i|_{P_j\cup P_\ell\cup P_m})=\operatorname{span}\{\chi_{P_j}+\chi_{P_\ell},\chi_{P_j}+\chi_{P_m}\}$).
--
--   This is the **deterministic core** of Sol's 'A Triple-Colour Ramsey Obstruction' (the probabilistic construction of the packets under a joint-balance hypothesis is not formalized here). In that note the packets have a common size $a$ with $3a\le k$; here only $|P_j\cup P_\ell\cup P_m|\le k$ is needed.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem seventeen_packet_contradiction {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (hb : ∀ A, #(L A) ≤ 2) (k : ℕ)
    (c : Fin 3 → C) (hc : Function.Injective c) (hu : ∀ i, c i ∉ L ∅)
    (hcov : ∀ i, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, c i ∈ L A)
    (p : Fin 3 → U → W)
    (hvalid : ∀ i, ∀ F : Finset U, 0 < #F → #F ≤ k → c i ∈ L F → (∀ F' ⊂ F, c i ∉ L F') →
      ∑ x ∈ F, p i x = 0)
    (hglob : ∀ i,
      k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range (p i))) + 2)
    (P : Fin 17 → Finset U) (hdisj : ∀ j l, j ≠ l → Disjoint (P j) (P l))
    (hne : ∀ j, (P j).Nonempty)
    (hsize : ∀ j l m, j ≠ l → j ≠ m → l ≠ m → #(P j ∪ P l ∪ P m) ≤ k)
    (hpair : ∀ i j l, j ≠ l → ∑ x ∈ P j ∪ P l, p i x = 0)
    (hker : ∀ i j l m, j ≠ l → j ≠ m → l ≠ m → ∀ G ⊆ P j ∪ P l ∪ P m,
      ∑ x ∈ G, p i x = 0 → G = ∅ ∨ G = P j ∪ P l ∨ G = P j ∪ P m ∨ G = P l ∪ P m) :
    False := by sorry

end Erdos624
