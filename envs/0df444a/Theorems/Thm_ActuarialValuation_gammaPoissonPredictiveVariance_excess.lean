-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPredictiveVariance_excess
-- name    : ActuarialValuation.gammaPoissonPredictiveVariance_excess
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:25:22.415067+00:00
-- url     : https://prove2.me/theorems/2f3382c1-88bb-457a-ba8e-c1592ad9d167
-- title:
--   Posterior predictive count variance exceeds conditional Poisson mean
-- statement:
--   The posterior predictive variance for a unit future Poisson exposure is the posterior mean plus the posterior Gamma variance. Since updated shape is positive and updated rate squared is positive, parameter uncertainty adds a nonnegative overdispersion term.
--
--   **Mathematical statement**
--
--   $$
--   \operatorname{Var}(N_{\rm new}\mid\text{data})=\hat\lambda+\alpha'/(\beta')^2\ge\hat\lambda
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPredictiveVariance_excess is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

theorem gammaPoissonPredictiveVariance_excess
  (a b e : ℝ) (c : ℕ)
  (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) :
  gammaPoissonPosteriorMean a b e c ≤
    gammaPoissonPosteriorMean a b e c +
      gammaPoissonPosteriorShape a c /
        (gammaPoissonPosteriorRate b e) ^ 2 := by sorry

end ActuarialValuation
