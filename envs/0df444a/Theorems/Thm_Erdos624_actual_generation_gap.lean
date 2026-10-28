-- Prove2me | Theorems.Thm_Erdos624_actual_generation_gap
-- name    : Erdos624.actual_generation_gap
-- status  : Proved
-- author  : @Ethan Cheung Wang
-- created : 2026-10-25T04:29:30.306065+00:00
-- url     : https://prove2.me/theorems/fc4b42d0-116a-42c0-8f0a-53d4d8664da0
-- title:
--   Uniform actual-generation theorem (A): $Z_u(T)\subseteq K_u(T)$ and $\dim K_u(T)-\dim Z_u(T)\le d-1$ (Erdős 624)
-- statement:
--   Setting: $U$ is a finite set of inputs, $L:\mathcal P(U)\to\mathcal P(C)$ an arbitrary list map (the actual colour lists), $k$ a natural number. A colour $u$ is *nonbottom* if $u\notin L(\varnothing)$ and *covering* if every $k$-subset $Y\subseteq U$ contains some $A$ with $u\in L(A)$. An *actual minimal witness* of $u$ is $F\subseteq U$ with $u\in L(F)$ and $u\notin L(F')$ for every $F'\subsetneq F$. A *valid label* for $u$ is a map $p:U\to V$ into an $\mathbb F_2$-vector space with $\sum_{x\in F}p(x)=0$ for every actual minimal witness $F$ with $1\le|F|\le k$. For $T\subseteq U$, $\operatorname{rk}(T)=\dim\operatorname{span}p(T)$ and $\operatorname{rk}(U)=\dim\operatorname{span}p(U)$ (the dimension of the valid parity space). For $T\subseteq U$ let $K_u(T)=\{\xi\in\mathbb F_2^T:\sum_{x\in T}\xi_x p(x)=0\}$ (the kernel of $\xi\mapsto\sum_x\xi_xp(x)$) and $Z_u(T)=\operatorname{span}\{\chi_F: F\subseteq T$ an actual minimal witness of $u$ with $1\le|F|\le k\}\le\mathbb F_2^T$. **Theorem (A).** If $u$ is nonbottom and covering and $p$ is a valid label with $\operatorname{rk}(U)\ge k-d$ (stated as $k\le\operatorname{rk}(U)+d$), then for **every** $T\subseteq U$ (no size restriction) $$Z_u(T)\subseteq K_u(T),\qquad \dim K_u(T)+1\le\dim Z_u(T)+d.$$
--
--   Source: 'Actual Witness Spans and Intrinsic Kernel Diversity', boxed (A). (There the labels live on a pool $V$; take $U=V$.)
--
--   Context: Erdős Problem 624 asks whether $H(n)-\log_2 n\to\infty$, where $H(n)$ is the least $m$ such that some $f:\mathcal P(X)\to X$ with $|X|=n$ satisfies $f[\mathcal P(Y)]=X$ for all $|Y|\ge m$. This is an auxiliary finite statement from Sol's Round 13 notes on the two-track (PAIR) case. It does **not** settle Erdős Problem 624, PAIR or Step 17; the initial near-critical population those notes start from is not established.
-- source:
--   Erdős Problem 624 (https://www.erdosproblems.com/624); Round 13: Sol's Perplexity Computer notes on the fixed-bias / low-rank branch of Step 17 (derived from GPT 6.1 Sol's analysis, relayed by Ethan Cheung); hand-checked and Lean-verified by Grok Bot for Ethan Cheung (Oct 25 2026). Auxiliary result only; does NOT settle PAIR / Step 17 / #624.

import Mathlib
open Finset

namespace Erdos624

theorem actual_generation_gap {U : Type*} [Fintype U] [DecidableEq U] {C : Type*} [DecidableEq C]
    {W : Type*} [AddCommGroup W] [Module (ZMod 2) W]
    (L : Finset U → Finset C) (k d : ℕ) (u : C) (hu : u ∉ L ∅)
    (hcov : ∀ Y : Finset U, #Y = k → ∃ A ⊆ Y, u ∈ L A)
    (p : U → W)
    (hvalid : ∀ F : Finset U, 0 < #F → #F ≤ k → u ∈ L F → (∀ F' ⊂ F, u ∉ L F') →
      ∑ x ∈ F, p x = 0)
    (hglob : k ≤ Module.finrank (ZMod 2) (Submodule.span (ZMod 2) (Set.range p)) + d)
    (T : Finset U) :
    Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0} ≤
      LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x)) ∧
    Module.finrank (ZMod 2) (LinearMap.ker (Fintype.linearCombination (ZMod 2) (fun x : T => p x))) + 1 ≤
      Module.finrank (ZMod 2) (Submodule.span (ZMod 2) {f : T → ZMod 2 | ∃ F : Finset U, F ⊆ T ∧ 0 < #F ∧ #F ≤ k ∧
        u ∈ L F ∧ (∀ F' ⊂ F, u ∉ L F') ∧ f = fun x : T => if x.1 ∈ F then (1 : ZMod 2) else 0}) + d := by sorry

end Erdos624
