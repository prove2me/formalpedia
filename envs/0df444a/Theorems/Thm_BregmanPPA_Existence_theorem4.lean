-- Prove2me | Theorems.Thm_BregmanPPA_Existence_theorem4
-- name    : BregmanPPA.Existence.theorem4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T17:19:48.29099+00:00
-- url     : https://prove2.me/theorems/31f1b200-1619-49ed-8795-baa6cd5020a8
-- title:
--   Theorem 4 — Bregman proximal point sequences exist when im ∇h = ℝⁿ, or im ∇h is open and 0 ∈ im T
-- statement:
--   Let $H$ be a finite-dimensional real inner product space (the paper's $\mathbb R^n$), let $T:H\to2^H$ be a maximal monotone operator, and let $h$ be a Bregman function with zone $S\supseteq\operatorname{dom}T$. Suppose that either
--
--   1. $\operatorname{im}\nabla h=H$, or
--   2. $\operatorname{im}\nabla h$ is open and $0\in\operatorname{im}T$,
--
--   where $\operatorname{im}\nabla h=\nabla h(S)$. Then for every sequence of positive scalars $\{c_k\}_{k\ge0}$ and every $x^0\in\operatorname{dom}\nabla h=S$ there is an infinite sequence $\{x^k\}_{k\ge0}$ starting at $x^0$ and conforming to the recursion (3),
--   $$
--   x^{k+1}=(\nabla h+c_kT)^{-1}\bigl(\nabla h(x^k)\bigr),\qquad k=0,1,2,\dots
--   $$
--   that is, $x^k\in S$ and $\tfrac1{c_k}\bigl(\nabla h(x^k)-\nabla h(x^{k+1})\bigr)\in T(x^{k+1})$ for every $k$.
--
--   Theorem 1 of the paper describes the behaviour of such sequences; this theorem gives conditions under which they exist at all. Without them the method can halt: the next iterate need not exist.
--
--   **Formalization Note** The scalars $c_k$ are not fixed by the statement and are quantified over all positive sequences (Theorem 1's extra condition $\inf_k c_k>0$ is not needed for existence). The hypothesis is $S\supseteq\operatorname{dom}T$ without closures, as printed. Recursion (3) is encoded through the equivalent inclusion (4) (p. 207) with all iterates in $S$, so the conclusion includes that every iterate stays in the zone. $\operatorname{im}\nabla h$ is the image of $S$ under $\nabla h$, not the range of Mathlib's total `gradient h`.
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 209, Theorem 4

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators
import Definitions.Def_DouglasRachfordPPA_GenDR_Operators
import Definitions.Def_BregmanPPA_Convergence_Model
import Definitions.Def_BregmanPPA_Existence_Operators

open ThreeOpSplitting.Convergence DouglasRachfordPPA.GenDR

namespace BregmanPPA.Existence

/-- Theorem 4 (p. 209): let `T` be maximal monotone and `h` a Bregman function with zone
`S ⊇ dom T`. If `im ∇h = ℝⁿ`, or `im ∇h` is open and `0 ∈ im T`, then for every sequence of
positive scalars `c k` and every `x⁰ ∈ dom ∇h = S`, an infinite sequence conforming to the
recursion (3) and starting at `x⁰` exists. -/
theorem theorem4 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [FiniteDimensional ℝ H] (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hdom : dom T ⊆ S)
    (hcase : gradient h '' S = Set.univ ∨
      (IsOpen (gradient h '' S) ∧ (0 : H) ∈ imOp T)) :
    ∀ c : ℕ → ℝ, (∀ k, 0 < c k) → ∀ x₀ ∈ S,
      ∃ x : ℕ → H, x 0 = x₀ ∧ IsBregmanPPARun S h T c x := by sorry

end BregmanPPA.Existence
