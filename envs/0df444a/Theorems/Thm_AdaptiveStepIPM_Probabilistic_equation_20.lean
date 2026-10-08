-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Probabilistic_equation_20
-- name    : AdaptiveStepIPM.Probabilistic.equation_20
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:22:53.902986+00:00
-- url     : https://prove2.me/theorems/6d556519-341f-48dd-87ae-bcac1351ec6d
-- title:
--   Equation (20) — Gaussian Euclidean norm lower bound
-- statement:
--   Let $\lambda_n$ be a standard Gaussian vector in $\mathbb R^{n-1}$. For every real $\varepsilon>0$,
--
--   $$
--   \Pr\!\left(\|\lambda_n\|_2\ge(1-\varepsilon)\sqrt{n-1}\right)\longrightarrow1
--   \quad\text{as }n\longrightarrow\infty.
--   $$
--
--   This supplies the denominator control when a uniform spherical vector is represented as $\lambda_n/\|\lambda_n\|_2$.
--
--   **Formalization Note** The Gaussian law is Mathlib's standard Gaussian on Euclidean space. The first few dimensions use Lean's total natural subtraction and do not affect the limit.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 15, Eq. (20); https://doi.org/10.1287/moor.18.4.964

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- Equation (20), the high dimensional Gaussian norm lower bound. -/
theorem equation_20 (ε : ℝ) (hε : 0 < ε) :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin (n - 1))))
        {w | (1 - ε) * Real.sqrt ((n - 1 : ℕ) : ℝ) ≤ ‖w‖}).toReal)
      atTop (nhds 1) := by sorry

end AdaptiveStepIPM.Probabilistic
