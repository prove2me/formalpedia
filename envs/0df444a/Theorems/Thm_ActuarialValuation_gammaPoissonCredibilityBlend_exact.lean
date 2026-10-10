-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonCredibilityBlend_exact
-- name    : ActuarialValuation.gammaPoissonCredibilityBlend_exact
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:25:02.129734+00:00
-- url     : https://prove2.me/theorems/951dc3da-07b2-4631-adc4-b4177bf8f5e7
-- title:
--   Positive-exposure credibility blend equals posterior mean
-- statement:
--   With positive prior rate and positive observed exposure, the observed claim frequency and collective mean are both well-defined. Substituting weight E/(β+E) and simplifying proves the exact Bayesian credibility decomposition of posterior mean (α+C)/(β+E).
--
--   **Mathematical statement**
--
--   $$
--   Z\,C/E+(1-Z)\alpha/\beta=(\alpha+C)/(\beta+E)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonCredibilityBlend_exact is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonCredibilityBlend
import Definitions.Def_actuarial_gammaPoissonExperienceWeight
import Definitions.Def_actuarial_gammaPoissonPosteriorMean

namespace ActuarialValuation

theorem gammaPoissonCredibilityBlend_exact
  (a b e : ℝ) (c : ℕ)
  (hb : 0 < b) (he : 0 < e) :
  gammaPoissonCredibilityBlend a b e c =
    gammaPoissonPosteriorMean a b e c := by sorry

end ActuarialValuation
