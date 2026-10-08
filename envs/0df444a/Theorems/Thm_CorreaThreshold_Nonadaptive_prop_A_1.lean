-- Prove2me | Theorems.Thm_CorreaThreshold_Nonadaptive_prop_A_1
-- name    : CorreaThreshold.Nonadaptive.prop_A_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T12:37:13.841409+00:00
-- url     : https://prove2.me/theorems/cacdc1f0-5420-4071-a8b4-c02b6d4d0edf
-- title:
--   Proposition A.1, p. 1470 — structure of a minimizer of f_M
-- statement:
--   Let $M$ be a nonempty finite index set and $a\le1$. Minimize the paper's function $f_M(x)$ over $x_i\ge0$ with $\sum_{i\in M}x_i\le a$. Every minimizer has equal nonzero coordinates and exhausts the constraint:
--
--   $$x_i,x_j>0\ \Longrightarrow\ x_i=x_j,\qquad \sum_{i\in M}x_i=a.$$
--
--   This identifies the shape of the extremal vector used to bound equation (5).
--
--   **Formalization Note** The condition $M\ne\varnothing$ excludes an empty-index counterexample to the asserted budget equality when $a>0$. At $a=0$, the unique feasible vector on $M$ is zero and the conclusion holds. Coordinates outside $M$ do not affect $f_M$.
-- source:
--   Correa, Foncea, Hoeksma, Oosterwijk, Vredeveld, Posted price mechanisms and optimal threshold strategies for random arrivals, Math. Oper. Res. 46 (2021), p. 1470, Proposition A.1; https://doi.org/10.1287/moor.2020.1105

import Mathlib
import Definitions.Def_CorreaThreshold_Nonadaptive_Bernoulli

namespace CorreaThreshold.Nonadaptive

/-- Proposition A.1: every constrained minimizer has equal nonzero coordinates and uses the budget. -/
theorem prop_A_1 {n : ℕ} [NeZero n]
    (M : Finset (Fin n)) (hM : M.Nonempty) (a : ℝ)
    (ha1 : a ≤ 1) (x : Fin n → ℝ)
    (hx : (∀ j ∈ M, 0 ≤ x j) ∧ ∑ j ∈ M, x j ≤ a)
    (hmin : ∀ y : Fin n → ℝ, (∀ j ∈ M, 0 ≤ y j) →
      ∑ j ∈ M, y j ≤ a → fM M x ≤ fM M y) :
    (∀ i ∈ M, ∀ j ∈ M, x i ≠ 0 → x j ≠ 0 → x i = x j) ∧
      ∑ j ∈ M, x j = a := by sorry

end CorreaThreshold.Nonadaptive
