-- Prove2me | Theorems.Thm_D1Bound5_ordinaryLog10_two_small_parameters
-- name    : D1Bound5.ordinaryLog10_two_small_parameters
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T23:12:20.960104+00:00
-- url     : https://prove2.me/theorems/0968cc14-abc7-4c30-840a-93028599cfbb
-- title:
--   Ordinary Log10 two small parameters
-- statement:
--   Auxiliary result `ordinaryLog10_two_small_parameters` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallHeightScalar.lean, lines 56-67, SHA-256 2fc4438e81abf1fb9766cd269fcc8b00c95036ba7e21a2aa00ca22bc65122f73. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5













theorem _root_.D1Bound5.ordinaryLog10_two_small_parameters :
    ordinaryLog10 1134 < (31/10 : ℝ) ∧
      -(9/10 : ℝ) < ordinaryLog10 (2/15) ∧
      ordinaryLog10 2277 < (17/5 : ℝ) := by sorry

end D1Bound5
end
