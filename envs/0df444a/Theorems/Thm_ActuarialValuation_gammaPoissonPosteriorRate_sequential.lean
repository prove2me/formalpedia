-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorRate_sequential
-- name    : ActuarialValuation.gammaPoissonPosteriorRate_sequential
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:23:09.037855+00:00
-- url     : https://prove2.me/theorems/10a4299b-7701-4cee-bce4-4428e962ad59
-- title:
--   Exposure batches update posterior rate additively
-- statement:
--   Sequential accumulation of two insured-exposure volumes yields the same posterior rate as adding the exposure batches together first. Order-independent exposure aggregation is an important validation of experience-rating data updates.
--
--   **Mathematical statement**
--
--   $$
--   (\beta+E)+F=\beta+(E+F)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorRate_sequential is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

theorem gammaPoissonPosteriorRate_sequential
  (b e f : ℝ) :
  gammaPoissonPosteriorRate (gammaPoissonPosteriorRate b e) f =
    gammaPoissonPosteriorRate b (e + f) := by sorry

end ActuarialValuation
