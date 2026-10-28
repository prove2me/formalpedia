-- Prove2me | Theorems.Thm_D1Bound5_two_small_M_window_brackets
-- name    : D1Bound5.two_small_M_window_brackets
-- status  : Proved
-- author  : @tp
-- created : 2026-10-23T22:58:42.670181+00:00
-- url     : https://prove2.me/theorems/fd64ae76-3de4-4619-8c89-e888d228bc90
-- title:
--   Two small M window brackets
-- statement:
--   Auxiliary result `two_small_M_window_brackets` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/TwoSmallMWindow.lean, lines 41-84, SHA-256 01923ebf8661b40e7df02a892c03d641336b952c4de01415c43f072023fbf04f. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions
import Definitions.Def_D1Bound5_TwoSmallHeightScalar_Definitions

section
namespace D1Bound5



theorem _root_.D1Bound5.two_small_M_window_brackets
    (C D : ℝ) (hC : (10 : ℝ)^100 ≤ C)
    (hlow : C^7/(10 : ℝ)^50 < D)
    (hhigh : ordinaryLog10 D < twoSmallHeightEnvelope (ordinaryLog10 C))
    (hD : 0 < D) :
    (10 : ℝ)^143*C^5 ≤ D ∧ D ≤ C^11/(10 : ℝ)^87 := by sorry

end D1Bound5
end
