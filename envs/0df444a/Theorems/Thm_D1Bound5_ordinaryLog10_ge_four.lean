-- Prove2me | Theorems.Thm_D1Bound5_ordinaryLog10_ge_four
-- name    : D1Bound5.ordinaryLog10_ge_four
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:45:21.560795+00:00
-- url     : https://prove2.me/theorems/4bd08beb-7aa9-47d8-9988-85003da42805
-- title:
--   Ordinary Log10 ge four
-- statement:
--   Auxiliary result `ordinaryLog10_ge_four` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/UnitPairHeightCutoff.lean, lines 11-15, SHA-256 0c2e2f5d6333fc3971f549ba84e0129a097627670f990f7ead321a035b9be11c. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic
import Definitions.Def_D1Bound5_OrdinaryLog10_Definitions

section
namespace D1Bound5



theorem _root_.D1Bound5.ordinaryLog10_ge_four {S : ℝ} (hS : 10000 ≤ S) :
    4 ≤ ordinaryLog10 S := by sorry





end D1Bound5
end
