-- Prove2me | Theorems.Thm_CauchyRiemannIndex_exists_contDiff_periodic_approx
-- name    : CauchyRiemannIndex.exists_contDiff_periodic_approx
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-17T16:35:14.773169+00:00
-- url     : https://prove2.me/theorems/eb56a0a8-ffb2-4835-9dc0-f1351b20fae5
-- title:
--   Smooth periodic functions are uniformly dense in continuous periodic functions
-- statement:
--   Let $f:\mathbb{R}\to\mathbb{R}$ be continuous and $1$-periodic, and let $\varepsilon>0$. Then there is a $C^\infty$, $1$-periodic function $g:\mathbb{R}\to\mathbb{R}$ with $|g(t)-f(t)|\le\varepsilon$ for all $t\in\mathbb{R}$.
--
--   This lets continuous loops on $S^1=\mathbb{R}/\mathbb{Z}$ (moduli, arguments, coefficients) be replaced by smooth loops that are uniformly close, for instance in deformation arguments for asymptotic operators.
--
--   **Formalization Note** Smoothness is `ContDiff ℝ ∞ g`; periodicity is `Function.Periodic g 1`.
-- source:
--   C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Lecture 5, §5.8, pp. 102-103

import Mathlib.Analysis.Calculus.ContDiff.Basic
import Mathlib.Algebra.Ring.Periodic

namespace CauchyRiemannIndex

open scoped ContDiff

/-- A continuous `1`-periodic real function is uniformly approximated, to any `ε > 0`, by a
smooth `1`-periodic function. -/
theorem exists_contDiff_periodic_approx (f : ℝ → ℝ) (hf : Continuous f)
    (hper : Function.Periodic f 1) (ε : ℝ) (hε : 0 < ε) :
    ∃ g : ℝ → ℝ, ContDiff ℝ ∞ g ∧ Function.Periodic g 1 ∧ ∀ t, |g t - f t| ≤ ε := by
  sorry

end CauchyRiemannIndex
