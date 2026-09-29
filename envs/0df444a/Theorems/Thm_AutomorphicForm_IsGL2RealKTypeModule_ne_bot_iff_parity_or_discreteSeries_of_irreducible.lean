-- Prove2me | Theorems.Thm_AutomorphicForm_IsGL2RealKTypeModule_ne_bot_iff_parity_or_discreteSeries_of_irreducible
-- name    : AutomorphicForm.IsGL2RealKTypeModule.ne_bot_iff_parity_or_discreteSeries_of_irreducible
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:52.366631+00:00
-- url     : https://prove2.me/theorems/f83c8f74-db52-5266-943f-31593f02a50b
-- title:
--   K-type support of an irreducible infinite-dimensional GL₂(ℝ)-module
-- statement:
--   Let $M$ be a complex vector space, $wt:\mathbb{Z}\to$ (submodules of $M$) a family of subspaces and $E,L,\varepsilon$ complex-linear endomorphisms of $M$ satisfying the structure `IsGL2RealKTypeModule`: the family $wt$ is an internal direct sum decomposition of $M$, $E$ maps $wt(n)$ into $wt(n+2)$, $L$ maps $wt(n)$ into $wt(n-2)$, $E(Lv)-L(Ev)=n\cdot v$ for every $v\in wt(n)$, $\varepsilon$ maps $wt(n)$ into $wt(-n)$, $\varepsilon\circ\varepsilon=\mathrm{id}$, and $\varepsilon$ followed by nothing else: $\varepsilon\circ E=L\circ\varepsilon$ (as the composite $\varepsilon\circ_{\mathbb C}E=L\circ_{\mathbb C}\varepsilon$). Assume in addition: each $wt(n)$ is finite-dimensional over $\mathbb C$; irreducibility in the sense of `IsIrreducibleGL2RealKTypeModule`, i.e. $M$ contains a nonzero vector and every subspace $W$ with $W\le\bigsqcup_n (W\cap wt(n))$ (the supremum of its weight parts) and $E(W),L(W),\varepsilon(W)\subseteq W$ equals $\bot$ or $\top$; and that $\{n : wt(n)\neq\bot\}$ is infinite. The conclusion has two parts. First, either there is $e\in\mathbb Z$ with $wt(n)\neq\bot\iff n\equiv e \pmod 2$ for all $n$, or there is $k\ge 2$ with $wt(n)\neq\bot\iff(|n|\ge k$ and $n\equiv k\pmod 2)$ for all $n$. Second, for every $k\ge 2$: there exists a nonzero $v\in wt(k)$ with $Lv=0$ if and only if $wt(n)\neq\bot\iff(|n|\ge k$ and $n\equiv k\pmod 2)$ holds for all $n$.
--
--   This is the combinatorial classification, in terms of $\mathrm{SO}(2)$-types, of the infinite-dimensional irreducible admissible $(\mathfrak{g},K)$-modules of $\mathrm{GL}_2(\mathbb{R})$: the weight support is either a full parity class (principal series and limits of discrete series) or the tail $\{|n|\ge k,\ n\equiv k \bmod 2\}$ of the discrete series of lowest weight $k\ge 2$, the latter case being detected by a lowest weight vector of weight $k$. It is used in the archimedean weight bookkeeping for automorphic forms, via [`AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre`](thm.html#AutomorphicForm.archOccursInClassOf_archWeightChar_iff_parity_or_discreteSeries_of_coversModCentre).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_IsGL2RealKTypeModule_ne_bot_iff_parity_or_discreteSeries_of_irreducible.lean

import Mathlib
import Definitions.Def_AutomorphicForm_GL2RealKTypeModule

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

open AutomorphicForm

theorem AutomorphicForm.IsGL2RealKTypeModule.ne_bot_iff_parity_or_discreteSeries_of_irreducible
    (M : Type*) [AddCommGroup M] [Module ℂ M]
    (wt : ℤ → Submodule ℂ M) (E L ε : M →ₗ[ℂ] M)
    (hM : IsGL2RealKTypeModule wt E L ε)
    (hadm : ∀ n : ℤ, FiniteDimensional ℂ (wt n))
    (hirr : IsIrreducibleGL2RealKTypeModule wt E L ε)
    (hinf : {n : ℤ | wt n ≠ ⊥}.Infinite) :
    ((∃ e : ℤ, ∀ n : ℤ, wt n ≠ ⊥ ↔ Even (n - e)) ∨
      (∃ k : ℤ, 2 ≤ k ∧ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) ∧
    (∀ k : ℤ, 2 ≤ k →
      ((∃ v ∈ wt k, v ≠ 0 ∧ L v = 0) ↔ ∀ n : ℤ, wt n ≠ ⊥ ↔ (k ≤ |n| ∧ Even (n - k)))) := by sorry
