-- Prove2me | Theorems.Thm_ActuarialValuation_gammaPoissonPosteriorMean_sequential
-- name    : ActuarialValuation.gammaPoissonPosteriorMean_sequential
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-09T14:23:46.342387+00:00
-- url     : https://prove2.me/theorems/7de01ab4-366c-4eb7-b510-3cc995e96d65
-- title:
--   Two experience periods give the same final posterior frequency as one combined period
-- statement:
--   The posterior frequency after one batch becomes the starting Gamma shape/rate for the next batch. Updating with a second batch of counts and exposure agrees exactly with a single posterior update using summed counts and summed exposures.
--
--   **Mathematical statement**
--
--   $$
--   \frac{(\alpha+C)+D}{(\beta+E)+F}=\frac{\alpha+(C+D)}{\beta+(E+F)}
--   $$
-- source:
--   Original derived actuarial identity from S. David Promislow, Fundamentals of Actuarial Mathematics (3rd ed., 2015), Chapter 24, Section 24.4, printed page 461 (Library PDF page 487), parent framework: Example 24.7 (Poisson–Gamma). Publisher https://www.oreilly.com/library/view/fundamentals-of-actuarial/9781118782521/; supporting reference https://openacttexts.github.io/LDAVer2/ChapCredibility.html. The specific Lean declaration ActuarialValuation.gammaPoissonPosteriorMean_sequential is a new algebraic specialisation, not quoted as a separately numbered source theorem.

import Mathlib.Data.Real.Basic
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Definitions.Def_actuarial_gammaPoissonPosteriorMean
import Definitions.Def_actuarial_gammaPoissonPosteriorShape
import Definitions.Def_actuarial_gammaPoissonPosteriorRate

namespace ActuarialValuation

theorem gammaPoissonPosteriorMean_sequential
  (a b e f : ℝ) (c d : ℕ) :
  gammaPoissonPosteriorMean
    (gammaPoissonPosteriorShape a c)
    (gammaPoissonPosteriorRate b e) f d =
  gammaPoissonPosteriorMean a b (e + f) (c + d) := by sorry

end ActuarialValuation
