-- Prove2me | Theorems.Thm_AdaptiveStepIPM_Probabilistic_gaussian_maximum
-- name    : AdaptiveStepIPM.Probabilistic.gaussian_maximum
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-06T15:21:20.280692+00:00
-- url     : https://prove2.me/theorems/a7851e10-511e-42f0-8103-fb204b45c2f3
-- title:
--   Gaussian coordinate maximum limit in the proof of Lemma 7
-- statement:
--   Let $\lambda'_n$ be a standard Gaussian vector in $\mathbb R^n$. The largest absolute coordinate obeys
--
--   $$
--   \Pr\!\left(\|\lambda'_n\|_\infty\le\sqrt{2\log(2n)}\right)
--   \longrightarrow1\quad\text{as }n\longrightarrow\infty.
--   $$
--
--   This is the extreme-value estimate used to control the numerator in the spherical-coordinate bound of Lemma 7.
--
--   **Formalization Note** The logarithm is natural, and the coordinate sup norm is distinguished from the Euclidean norm.
-- source:
--   Mizuno, Todd, Ye, On adaptive-step primal-dual interior-point algorithms for linear programming, Cornell ORIE Technical Report No. 944 (1990, rev. 1991), p. 15, proof of Lemma 7, displayed Gaussian-maximum limit; https://doi.org/10.1287/moor.18.4.964

import Definitions.Def_AdaptiveStepIPM_Probabilistic_Model

open MeasureTheory ProbabilityTheory Filter

namespace AdaptiveStepIPM.Probabilistic

/-- The Gaussian maximum limit used in the proof of Lemma 7. -/
theorem gaussian_maximum :
    Tendsto (fun n : ℕ =>
      ((stdGaussian (EuclideanSpace ℝ (Fin n)))
        {w | supNorm w ≤ Real.sqrt (2 * Real.log (2 * (n : ℝ)))}).toReal)
      atTop (nhds 1) := by sorry

end AdaptiveStepIPM.Probabilistic
