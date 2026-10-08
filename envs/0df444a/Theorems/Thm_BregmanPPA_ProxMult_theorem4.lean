-- Prove2me | Theorems.Thm_BregmanPPA_ProxMult_theorem4
-- name    : BregmanPPA.ProxMult.theorem4
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-06T19:13:53.796707+00:00
-- url     : https://prove2.me/theorems/d4ffefaf-2180-4b77-9950-e6e844e47f67
-- title:
--   Theorem 4 — Bregman proximal point sequences exist when im ∇h is everything, or is open and 0 ∈ im T
-- statement:
--   Let $T$ be a maximal monotone operator on a finite-dimensional real inner product space $H$, and let $h$ be a Bregman function with zone $S\supseteq\operatorname{dom}T$. If either
--
--   1. $\operatorname{im}\nabla h=H$, or
--   2. $\operatorname{im}(\nabla h)$ is open and $0\in\operatorname{im}T$,
--
--   then for every sequence of positive scalars $c_k$ bounded away from zero and every $x^0\in\operatorname{dom}\nabla h=S$, an infinite sequence $\{x^k\}$ starting at $x^0$ and conforming to the recursion (3) exists.
--
--   The proof of Theorem 8 applies case 1 on $\mathbb R^{n+m}$ to obtain the existence clause.
--
--   **Formalization Note** Restated over a finite-dimensional inner product space (the paper's $\mathbb R^n$). $\operatorname{im}\nabla h$ is the image $\nabla h(S)$ and $\operatorname{im}T=\{y:\exists x,\ y\in T x\}$. The paper's recursion (3) does not fix $c_k$; the statement quantifies over every sequence bounded away from zero, as in the Section 2 setup of recursion (3).
-- source:
--   Eckstein, Nonlinear proximal point algorithms using Bregman functions, with applications to convex programming, Math. Oper. Res. 18(1) (1993), p. 209, Theorem 4

import Mathlib
import Definitions.Def_BregmanPPA_Convergence_Model

open ThreeOpSplitting.Convergence

namespace BregmanPPA.ProxMult

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [FiniteDimensional ℝ H]

/-- Theorem 4, p. 209, restated: `T` maximal monotone, `h` a Bregman function with zone
`S ⊇ dom T`. If `im ∇h = H`, or `im ∇h` is open and `0 ∈ im T`, then for all positive `c k` bounded away from zero
and every `x⁰ ∈ dom ∇h = S` an infinite sequence conforming to (3) and starting at `x⁰` exists. -/
theorem theorem4 (T : H → Set H) (S : Set H) (h : H → ℝ)
    (hT : IsMaximalMonotone T) (hh : BregmanPPA.Convergence.IsBregmanFunction S h) (hdom : dom T ⊆ S)
    (hcase : gradient h '' S = Set.univ ∨
      (IsOpen (gradient h '' S) ∧ (0 : H) ∈ {y : H | ∃ z, y ∈ T z})) :
    ∀ c : ℕ → ℝ, (∀ k, 0 < c k) →
      (∃ ε : ℝ, 0 < ε ∧ ∀ k, ε ≤ c k) → ∀ x₀ ∈ S,
      ∃ x : ℕ → H, x 0 = x₀ ∧ BregmanPPA.Convergence.IsBregmanPPARun S h T c x := by sorry

end BregmanPPA.ProxMult
