-- Prove2me | Theorems.Thm_ContDiff_exists_weighted_cutoff_deriv_bound
-- name    : ContDiff.exists_weighted_cutoff_deriv_bound
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-16T15:47:24.419966+00:00
-- url     : https://prove2.me/theorems/c3d33902-90b0-4a3e-adb2-a866996535da
-- title:
--   Weighted derivative bounds for a smooth cutoff with constant tails
-- statement:
--   Let $q:\mathbb R\to\mathbb R$ be smooth, equal to zero on $(-\infty,1]$ and equal to one on $[2,\infty)$. For every nonnegative integer $r$ there is a nonnegative constant $D$ such that
--   $$|q^{(r)}(s)|\,|s|^r\le D\qquad(s\in\mathbb R).$$
--   The assertion includes $r=0$ and imposes no prescribed size bound in the transition interval. It is a uniform coefficient estimate for rescaled cutoff arguments.
-- source:
--   Elementary consequence of compactness and locality of derivatives. Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas, Filter.EventuallyEq.iteratedDeriv_eq, https://github.com/leanprover-community/mathlib4/blob/0df444a360eaa60ab8c11dca51a86af692955474/Mathlib/Analysis/Calculus/IteratedDeriv/Lemmas.lean ; Mathlib.Analysis.Normed.Group.Bounded, IsCompact.exists_bound_of_continuousOn. Derived auxiliary for the normal-cutoff Taylor-Leibniz estimate; not a quotation of a separate source theorem.

import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
import Mathlib.Analysis.Normed.Group.Bounded
import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
open Filter
open scoped ContDiff Topology
set_option autoImplicit false

theorem ContDiff.exists_weighted_cutoff_deriv_bound (q : ℝ → ℝ) (hq : ContDiff ℝ ∞ q)
    (hlo : ∀ s : ℝ, s ≤ 1 → q s = 0)
    (hhi : ∀ s : ℝ, 2 ≤ s → q s = 1) (r : ℕ) :
    ∃ D : ℝ, 0 ≤ D ∧ ∀ s : ℝ, ‖iteratedDeriv r q s‖ * ‖s‖ ^ r ≤ D := by sorry
