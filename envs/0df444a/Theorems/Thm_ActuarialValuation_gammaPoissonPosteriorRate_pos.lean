-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorRate_pos
-- name    : ActuarialValuation.gammaPoissonPosteriorRate_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:22:00.470324+00:00
-- url     : https://prove2.me/theorems/27f244ed-0a29-4a47-8cd2-d3c87eec6b95
-- title:
--   Positive prior rate and nonnegative exposure preserve positive rate
-- statement:
--   The posterior rate is the sum of a positive Gamma prior rate and a nonnegative observation exposure. Its positivity guarantees that the posterior frequency and credibility expressions use a nonzero denominator.
--
--   **Mathematical statement**
--
--   $$
--   \beta>0,\ E\ge0\Rightarrow\beta'>0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorRate_pos is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

theorem gammaPoissonPosteriorRate_pos (b e : ℝ)
  (hb : 0 < b) (he : 0 ≤ e) :
  0 < gammaPoissonPosteriorRate b e := by sorry

end ActuarialValuation
