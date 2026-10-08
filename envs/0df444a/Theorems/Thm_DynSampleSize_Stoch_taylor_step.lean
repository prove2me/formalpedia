-- Prove2me | Theorems.Thm_DynSampleSize_Stoch_taylor_step
-- name    : DynSampleSize.Stoch.taylor_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T10:28:45.048123+00:00
-- url     : https://prove2.me/theorems/826089a2-08f0-4c0b-904b-19de85c48e61
-- title:
--   §4.2, p. 11 — Taylor bound for a step of length $1/L$ along any vector $g$
-- statement:
--   Let $J:\mathbb R^m\to\mathbb R$ satisfy (4.2) with constants $0<\lambda<L$. Then for every point $w$ and every vector $g\in\mathbb R^m$,
--
--   $$
--   J\!\left(w-\tfrac1L g\right)\;\le\;J(w)-\frac1L\nabla J(w)^Tg+\frac1{2L}\|g\|^2 .
--   $$
--
--   Applied with $w=w_k$ and $g=g_k$, this is the display "by Taylor's theorem and (4.2)" on p. 11 bounding $J(w_{k+1})$ for the iteration (4.24); it holds for every realisation of the batch gradient, and the expectation is taken afterwards.
-- source:
--   Byrd, Chin, Nocedal, Wu, Sample size selection in optimization methods for machine learning, Math. Program. (2012), doi:10.1007/s10107-012-0572-5 — authors' version of 18 Oct 2011, p. 11, unnumbered display after 'We have by Taylor's theorem and (4.2) that'

import Mathlib
import Definitions.Def_DynSampleSize_Stoch_UniformConvexity

namespace DynSampleSize.Stoch

/-- §4.2, p. 11 (display after "We have by Taylor's theorem and (4.2) that"): for every point `w`
and every vector `g`, `J(w − g/L) ≤ J(w) − (1/L)∇J(w)ᵀg + (1/(2L))‖g‖²`. -/
theorem taylor_step {m : ℕ} (J : EuclideanSpace ℝ (Fin m) → ℝ) (lam L : ℝ)
    (hJ : UniformlyConvex J lam L) (w g : EuclideanSpace ℝ (Fin m)) :
    J (w - (1 / L) • g) ≤ J w - (1 / L) * inner ℝ (gradient J w) g + 1 / (2 * L) * ‖g‖ ^ 2 := by sorry

end DynSampleSize.Stoch
