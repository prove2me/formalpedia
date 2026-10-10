-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorShape_pos
-- name    : ActuarialValuation.gammaPoissonPosteriorShape_pos
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:21:48.362993+00:00
-- url     : https://prove2.me/theorems/b4e8dc64-2ccf-44c5-acf3-bf9f62198215
-- title:
--   Positive Gamma shape remains positive after observing claims
-- statement:
--   The observed count is a natural number, so its real cast is nonnegative. Adding it to strictly positive prior shape yields a strictly positive posterior Gamma shape.
--
--   **Mathematical statement**
--
--   $$
--   \alpha>0,\ C\ge0\Rightarrow\alpha'>0
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorShape_pos is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorShape

namespace ActuarialValuation

theorem gammaPoissonPosteriorShape_pos (a : ℝ) (c : ℕ)
  (ha : 0 < a) : 0 < gammaPoissonPosteriorShape a c := by sorry

end ActuarialValuation
