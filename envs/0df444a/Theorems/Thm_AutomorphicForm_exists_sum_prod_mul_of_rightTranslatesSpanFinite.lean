-- Prove2me | Theorems.Thm_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite
-- name    : AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:28:55.646135+00:00
-- url     : https://prove2.me/theorems/bcea9a57-4813-56db-96e4-2c59ae7748ed
-- title:
--   Tensor splitting of a right Kᵢ-finite function
-- statement:
--   Let $G$ be a group, let $n \in \mathbb{N}$ and let $K_0,\dots,K_{n-1}$ be subgroups of $G$, indexed by `Fin n`, which commute elementwise across distinct indices: for $i \neq j$, every $x \in K_i$ and $y \in K_j$ satisfy $xy = yx$. Let $f \colon G \to \mathbb{C}$ be a function such that for each $i$ there is a finite set $s$ of functions $G \to \mathbb{C}$ with $x \mapsto f(xk)$ in the $\mathbb{C}$-span of $s$ for every $k \in K_i$. Then there are $N \in \mathbb{N}$ and families $a_{m,i} \colon G \to \mathbb{C}$ and $b_m \colon G \to \mathbb{C}$, for $m < N$ and $i < n$, such that: each $a_{m,i}$ lies in the $\mathbb{C}$-span of the two-sided translates $g \mapsto f(xgh)$ with $x \in G$ arbitrary and $h$ in the subgroup $\bigsqcup_j K_j$ (the supremum of the $K_j$); each $a_{m,i}$ again has the stated right finiteness property with respect to $K_i$, i.e. there is a finite set $t$ of functions whose span contains $g \mapsto a_{m,i}(gk')$ for all $k' \in K_i$; each $b_m$ lies in the $\mathbb{C}$-span of the right translates $x \mapsto f(xh)$ with $h \in \bigsqcup_j K_j$; and for every $x \in G$ and every choice $k \colon \mathrm{Fin}\, n \to G$ with $k_i \in K_i$ for all $i$, the ordered product satisfies $f\bigl(x\, k_0 k_1 \cdots k_{n-1}\bigr) = \sum_{m<N} \bigl(\prod_{i<n} a_{m,i}(k_i)\bigr)\, b_m(x)$, the product $k_0 \cdots k_{n-1}$ being that of the list `(List.ofFn k)`.
--
--   This is the finite-dimensionality argument behind separating variables in a right $K$-finite function: a function whose right translates under each of several commuting subgroups span a finite-dimensional space decomposes as a finite sum of products of functions of the separate variables, with the factors again drawn from translates of $f$. It is used in the treatment of archimedean $K$-finiteness and smoothness of automorphic forms and in the estimate for Whittaker-type integrals over unipotent subgroups against an additive character.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_AutomorphicForm_exists_sum_prod_mul_of_rightTranslatesSpanFinite.lean

import Mathlib.Algebra.Module.Pi
import Mathlib.LinearAlgebra.Span.Defs
import Mathlib.Data.Complex.Basic

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem AutomorphicForm.exists_sum_prod_mul_of_rightTranslatesSpanFinite
    {G : Type*} [Group G] {n : ℕ} (K : Fin n → Subgroup G)
    (hcomm : ∀ i j, i ≠ j → ∀ x ∈ K i, ∀ y ∈ K j, Commute x y)
    (f : G → ℂ)
    (hf : ∀ i, ∃ s : Finset (G → ℂ), ∀ k ∈ K i,
      (fun x => f (x * k)) ∈ Submodule.span ℂ (s : Set (G → ℂ))) :
    ∃ (N : ℕ) (a : Fin N → Fin n → G → ℂ) (b : Fin N → G → ℂ),
      (∀ m i, a m i ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ x h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun g => f (x * g * h)}) ∧
      (∀ m i, ∃ t : Finset (G → ℂ), ∀ k' ∈ K i,
          (fun g => a m i (g * k')) ∈ Submodule.span ℂ (t : Set (G → ℂ))) ∧
      (∀ m, b m ∈ Submodule.span ℂ
          {ψ : G → ℂ | ∃ h : G, h ∈ (⨆ j, K j : Subgroup G) ∧ ψ = fun x => f (x * h)}) ∧
      ∀ (x : G) (k : Fin n → G), (∀ i, k i ∈ K i) →
        f (x * (List.ofFn k).prod) = ∑ m, (∏ i, a m i (k i)) * b m x := by sorry
