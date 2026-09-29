-- Prove2me | Theorems.Thm_Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero
-- name    : Complex.countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/a90312e7-73b6-5300-aa39-8487e202e4d4
-- title:
--   Countability of the zeros in a right half-plane
-- statement:
--   Let $f : \mathbb{C} \to \mathbb{C}$ be a function and $\sigma$ a real number. Suppose $f$ is differentiable (in the complex sense) on the open right half-plane $\{s \in \mathbb{C} : \sigma < \operatorname{Re} s\}$, in the sense of `DifferentiableOn ℂ`, and suppose there exists at least one point $s$ with $\sigma < \operatorname{Re} s$ at which $f(s) \neq 0$. Then the set of $s \in \mathbb{C}$ satisfying both $\sigma < \operatorname{Re} s$ and $f(s) = 0$ is countable, in the sense of `Set.Countable`. Note that $f$ is required to be defined on all of $\mathbb{C}$ but is constrained only on the half-plane, so the conclusion concerns only the zeros lying in the half-plane; no hypothesis is imposed on the behaviour of $f$ on or to the left of the line $\operatorname{Re} s = \sigma$, and the non-vanishing hypothesis is the negation of $f$ vanishing identically on the half-plane.
--
--   This is the standard consequence of the identity theorem: a holomorphic function on a right half-plane which is not identically zero there has at most countably many zeros in that half-plane. It is used in the Rankin–Selberg part of the Langlands–Tunnell input, where a combination of pure translates of a finite family of archimedean integrals must be chosen so that a global integral is non-vanishing.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero.lean

import Mathlib.Analysis.Complex.CauchyIntegral
import Mathlib.Analysis.Analytic.IsolatedZeros
import Mathlib.Analysis.Analytic.Uniqueness
import Mathlib.Analysis.Complex.Convex
import Mathlib.Topology.Bases

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.countable_setOf_re_gt_and_eq_zero_of_differentiableOn_of_exists_ne_zero
    (f : ℂ → ℂ) (σ : ℝ)
    (hf : DifferentiableOn ℂ f {s : ℂ | σ < s.re})
    (hne : ∃ s : ℂ, σ < s.re ∧ f s ≠ 0) :
    Set.Countable {s : ℂ | σ < s.re ∧ f s = 0} := by sorry
