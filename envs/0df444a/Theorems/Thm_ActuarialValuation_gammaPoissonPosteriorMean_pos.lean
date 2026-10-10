-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorMean_pos
-- name    : ActuarialValuation.gammaPoissonPosteriorMean_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:22:13.357125+00:00
-- url     : https://prove2.me/theorems/7850b798-6c4e-42c3-b12b-a3ca29b6d81f
-- title:
--   Positive shape and rate imply a positive posterior claim frequency
-- statement:
--   The updated shape and rate are strictly positive under the Gamma-Poisson parameter assumptions. Their quotient is therefore a positive posterior claim frequency per unit of exposure.
--
--   **Mathematical statement**
--
--   $$
--   \hat\lambda>0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorMean_pos is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

theorem gammaPoissonPosteriorMean_pos
  (a b e : ℝ) (c : ℕ)
  (ha : 0 < a) (hb : 0 < b) (he : 0 ≤ e) :
  0 < gammaPoissonPosteriorMean a b e c := by sorry

end ActuarialValuation
