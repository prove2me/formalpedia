-- Prove2me | Theorems.Thm_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres
-- name    : ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/25be711b-0c5d-5caf-9357-148d231fc367
-- title:
--   Atom-free functionals pull back along coordinatewise finite-fibre maps
-- statement:
--   Let $\iota_K,\iota_L$ be index types, let $X_K\subseteq(\mathbb{C}\times\mathbb{C})^{\iota_K}$ be a compact set, let $X\subseteq(\mathbb{C}\times\mathbb{C})^{\iota_L}$ be an arbitrary set, let $T$ be a finite set of indices in $\iota_K$, and let $w'\colon\iota_K\to\iota_L$. Suppose given maps $B_v\colon\mathbb{C}\times\mathbb{C}\to\mathbb{C}\times\mathbb{C}$ for $v\in\iota_K$ such that, for every $v\in T$, $B_v$ is continuous and every fibre $B_v^{-1}(\{c\})$ is finite, and a continuous map $\mathrm{bc}\colon X_K\to X$ satisfying $\mathrm{bc}(x)(w'v)=B_v(x(v))$ for all $x\in X_K$ and $v\in T$. Let $\Lambda\colon C(X_K,\mathbb{C})\to\mathbb{C}$ be a continuous $\mathbb{C}$-linear functional with the following property: for every $\tau\in(\mathbb{C}\times\mathbb{C})^{\iota_K}$ and every $\varepsilon>0$ there are sets $U_v\subseteq\mathbb{C}\times\mathbb{C}$ with $U_v$ open and $\tau(v)\in U_v$ for all $v\in T$, such that every $g\in C(X_K,\mathbb{C})$ with $\|g(y)\|\le 1$ for all $y$ and with $g(y)=0$ whenever $y(v)\notin U_v$ for some $v\in T$ satisfies $\|\Lambda g\|<\varepsilon$. The conclusion is the same property for the pulled-back functional: for every $\tau$ and every $\varepsilon>0$ there are open sets $U_v\ni\tau(v)$ ($v\in T$) such that every $g\in C(X,\mathbb{C})$ with $\|g(y)\|\le 1$ for all $y$ and with $g(y)=0$ whenever $y(w'v)\notin U_v$ for some $v\in T$ satisfies $\|\Lambda(g\circ\mathrm{bc})\|<\varepsilon$.
--
--   This is a point-set topology transfer statement: absence of atomic mass on the cylinders cut out at the coordinates $v\in T$ is inherited by the pullback $g\mapsto\Lambda(g\circ\mathrm{bc})$ along a map whose $T$-coordinates are computed by continuous maps with finite fibres, the cylinders now being read at the coordinates $w'v$. It is used in the construction of continuous functionals on spaces of Satake parameters with prescribed values on monomials, and in the selection of atoms for Hecke-word sums of twisted cut traces.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_ContinuousLinearMap_noAtomicMass_comp_of_finite_fibres.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

set_option autoImplicit false

theorem ContinuousLinearMap.noAtomicMass_comp_of_finite_fibres
    {ιK ιL : Type} (XK : Set (ιK → ℂ × ℂ)) (hXKc : IsCompact XK) (X : Set (ιL → ℂ × ℂ)) (T : Finset ιK)
    (w' : ιK → ιL)
    (B : ιK → ℂ × ℂ → ℂ × ℂ) (hBc : ∀ v ∈ T, Continuous (B v))
    (hBf : ∀ v ∈ T, ∀ c : ℂ × ℂ, ((B v) ⁻¹' {c}).Finite)
    (bc : C(XK, X))
    (hbc : ∀ (x : XK), ∀ v ∈ T, ((bc x : X) : ιL → ℂ × ℂ) (w' v) = B v ((x : ιK → ℂ × ℂ) v))
    (Λ : C(XK, ℂ) →L[ℂ] ℂ)
    (hΛ : ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(XK, ℂ), (∀ y : XK, (∃ v ∈ T, (y : ιK → ℂ × ℂ) v ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ g‖ < ε) :
    ∀ (τ : ιK → ℂ × ℂ), ∀ ε > (0 : ℝ), ∃ U : ιK → Set (ℂ × ℂ), (∀ v ∈ T, IsOpen (U v) ∧ τ v ∈ U v) ∧
      ∀ g : C(X, ℂ), (∀ y : X, (∃ v ∈ T, (y : ιL → ℂ × ℂ) (w' v) ∉ U v) → g y = 0) → (∀ y, ‖g y‖ ≤ 1) →
        ‖Λ (g.comp bc)‖ < ε := by sorry
