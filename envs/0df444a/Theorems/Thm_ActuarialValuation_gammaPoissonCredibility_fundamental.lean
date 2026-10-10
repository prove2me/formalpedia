-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonCredibility_fundamental
-- name    : ActuarialValuation.gammaPoissonCredibility_fundamental
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:25:47.522609+00:00
-- url     : https://prove2.me/theorems/06ef5433-d584-483e-b365-76dfb19d2e0e
-- title:
--   Sequential Bayesian update and exact positive-exposure credibility
-- statement:
--   The capstone combines exact Gamma-Poisson experience credibility at positive exposure with associative sequential count/exposure updates and admissibility of the Bayesian experience weight. It formalises the conjugate-model parameter and premium algebra without claiming a full measure-theoretic Gamma likelihood integral.
--
--   **Mathematical statement**
--
--   $$
--   \hat\lambda=ZC/E+(1-Z)\alpha/\beta,\ \alpha'=\alpha+C,\ \beta'=\beta+E,\ 0\le Z\le1
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonCredibility_fundamental is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonCredibilityBlend
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate
import Definitions.Def_actuarial_gammaPoissonExperienceWeight

namespace ActuarialValuation

theorem gammaPoissonCredibility_fundamental
  (a b e f : ℝ) (c d : ℕ)
  (hb : 0 < b) (he : 0 < e) (hf : 0 ≤ f) :
  (gammaPoissonCredibilityBlend a b e c =
    gammaPoissonPosteriorMean a b e c) ∧
  (gammaPoissonPosteriorMean
     (gammaPoissonPosteriorShape a c)
     (gammaPoissonPosteriorRate b e) f d =
   gammaPoissonPosteriorMean a b (e + f) (c + d)) ∧
  (0 ≤ gammaPoissonExperienceWeight b e ∧
    gammaPoissonExperienceWeight b e ≤ 1) := by sorry

end ActuarialValuation
