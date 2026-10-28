-- Prove2me | Theorems.Thm_Erdos624_every_face_hidden_generation
-- name    : Erdos624.every_face_hidden_generation
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:44:02.693308+00:00
-- url     : https://prove2.me/theorems/c31ad547-55d3-41bf-8e52-da2b28ff8f04
-- title:
--   Every-face hidden-generation bound (G): on each $k$-face few colours with $\rho_u\le k-d-1$ have $\gamma_u(Y)\le H$ (Erdős 624)
-- statement:
--   Let $U$ be a finite set, $L:\mathcal P(U)\to\mathcal P(C)$ with $|L(A)|\le b$, and $S$ a finite set of nonbottom colours ($u\notin L(\varnothing)$) each attained inside every $k$-subset of $U$. For $u\in S$ let $Z_u(U)\le\mathbb F_2^U$ be the span of the indicator vectors $\chi_F$ of the actual minimal witnesses $F$ of $u$ with $1\le|F|\le k$ ($u\in L(F)$, $u\notin L(F')$ for $F'\subsetneq F$), and for a $k$-set $Y$ let $Z_u(Y)$ be the span of those with $F\subseteq Y$, and $\mathbb F_2^Y=\{f:f(x)=0\ \forall x\notin Y\}$ (written as the kernel of restriction to $U\setminus Y$). Put $\rho_u=|U|-\dim Z_u(U)$ and $\gamma_u(Y)=\dim(Z_u(U)\cap\mathbb F_2^Y)-\dim Z_u(Y)$.
--
--   **Theorem.** For every $Y$ with $|Y|=k$ and integers $0\le H<d$,$$(d-H)\cdot\#\{u\in S:\ \rho_u\le k-d-1,\ \dim(Z_u(U)\cap\mathbb F_2^Y)\le\dim Z_u(Y)+H\}+|S|\le b\,(2^k-1).$$(Both conditions are stated without subtraction: $|U|+d+1\le\dim Z_u(U)+k$ and $\dim(Z_u(U)\cap\mathbb F_2^Y)\le\dim Z_u(Y)+H$.)
--
--   Source: 'The Larger-Deficit Case and a Rare-Pair Barrier', boxed (G). With $S=C\setminus L(\varnothing)$, $|S|\ge n-b$, $n=2^k=|U|$ this gives $\#\{u\notin E_d:\gamma_u(Y)\le H\}\le\lfloor(b-1)n/(d-H)\rfloor$, i.e. (G) after adding the $M_d=|E_d|$ colours with $\rho_u\ge k-d$. This is a necessary condition for a hypothetical full cover, not a contradiction.
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem every_face_hidden_generation {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    (L : Finset U → Finset C) (b k d H : ℕ) (hb : ∀ A, #(L A) ≤ b)
    (S : Finset C) (hu : ∀ u ∈ S, u ∉ L ∅)
    (hcov : ∀ u ∈ S, ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (Y : Finset U) (hY : #Y = k) (hH : H < d) :
    #(S.filter (fun u =>
      Fintype.card U + d + 1 ≤
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {f : U → ZMod 2 | ∃ F : Finset U, 0 < #F ∧
          #F ≤ k ∧ u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x => if x ∈ F then 1 else 0}) + k ∧
      Module.finrank (ZMod 2) (↥((Submodule.span (ZMod 2) {f : U → ZMod 2 | ∃ F : Finset U, 0 < #F ∧
          #F ≤ k ∧ u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x => if x ∈ F then 1 else 0}) ⊓
        LinearMap.ker (LinearMap.funLeft (ZMod 2) (ZMod 2) (fun x : {x // x ∉ Y} => x.1)) : Submodule (ZMod 2) (U → ZMod 2))) ≤
        Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {f : U → ZMod 2 | ∃ F : Finset U, F ⊆ Y ∧
          0 < #F ∧ #F ≤ k ∧ u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧
          f = fun x => if x ∈ F then 1 else 0}) + H)) * (d - H) + #S ≤ b * (2 ^ k - 1) := by sorry

end Erdos624
