-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorShape_sequential
-- name    : ActuarialValuation.gammaPoissonPosteriorShape_sequential
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:22:51.965614+00:00
-- url     : https://prove2.me/theorems/b53fecf8-d447-43d8-9a0e-2ba10711e1b7
-- title:
--   Claim counts update posterior shape additively
-- statement:
--   Processing two nonnegative claim-count batches in sequence increases Gamma shape by each observed count. It gives the same result as combining the claim counts before a single posterior update.
--
--   **Mathematical statement**
--
--   $$
--   (\alpha+C)+D=\alpha+(C+D)
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorShape_sequential is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorShape

namespace ActuarialValuation

theorem gammaPoissonPosteriorShape_sequential
  (a : ℝ) (c d : ℕ) :
  gammaPoissonPosteriorShape (gammaPoissonPosteriorShape a c) d =
    gammaPoissonPosteriorShape a (c + d) := by sorry

end ActuarialValuation
