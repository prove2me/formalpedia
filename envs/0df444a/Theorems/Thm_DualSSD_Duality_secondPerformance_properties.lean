-- Prove2me | Theorems.Thm_DualSSD_Duality_secondPerformance_properties
-- name    : DualSSD.Duality.secondPerformance_properties
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-27T17:36:19.522317+00:00
-- url     : https://prove2.me/theorems/d438fe1b-6c1a-481e-84e6-b197f52b26e0
-- title:
--   §2, p. 62 — $F_X^{(2)}$ is continuous, convex, nonnegative, and nondecreasing
-- statement:
--   Let $X$ be a random variable with $\mathbb E|X|<\infty$. Then the second performance function
--   $$F_X^{(2)}(\eta)=\int_{-\infty}^{\eta}\mathbb P\{X\le\xi\}\,d\xi$$
--   is continuous, convex, nonnegative, and nondecreasing on $\mathbb R$.
--
--   Continuity (hence closedness) and convexity are what make $F_X^{(2)}$ equal to its own biconjugate, which the paper uses in Theorem 3.1(ii).
--
--   **Formalization Note** The integrability hypothesis is the paper's standing assumption $\mathbb E|X|<\infty$.
-- source:
--   Ogryczak, Ruszczyński, Dual Stochastic Dominance and Related Mean-Risk Models, SIAM J. Optim. 13 (2002), p. 62, sentence after eq. (2.4)

import Mathlib
import Definitions.Def_DualSSD_Shared_secondPerformance

namespace DualSSD.Duality

open MeasureTheory

/-- Ogryczak–Ruszczyński 2002, §2, p. 62 (sentence after (2.4)): for `E|X| < ∞`, the second
performance function `F_X^(2)` is continuous, convex, nonnegative, and nondecreasing. -/
theorem secondPerformance_properties {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) [IsProbabilityMeasure P] (X : Ω → ℝ) (hX : Integrable X P) :
    Continuous (Shared.secondPerformance P X) ∧ ConvexOn ℝ Set.univ (Shared.secondPerformance P X) ∧
      (∀ η : ℝ, 0 ≤ Shared.secondPerformance P X η) ∧ Monotone (Shared.secondPerformance P X) := by sorry

end DualSSD.Duality
