-- Prove2me | Theorems.Thm_D1Bound5_smallPairPilotTraceZeroNoTriangle_41_checked
-- name    : D1Bound5.smallPairPilotTraceZeroNoTriangle_41_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:54.578893+00:00
-- url     : https://prove2.me/theorems/5929b1f1-17de-4269-be40-e7a6fbfe60d1
-- title:
--   Small Pair Pilot Trace Zero No Triangle 41 checked
-- statement:
--   The original triangle predicate, obtained from the actual arithmetic no-three theorem and the linear trace-coordinate certificate.
-- source:
--   D1Bound5/SmallPairTraceZeroPilot41.lean, lines 15-21, SHA-256 5873e50be7d81103b7dc1e77ba68f8e8b774645e2c18a7075508d07bfc9ad4c6. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.Complex.Norm
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.GCD
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_SmallPairBipartitePilotData41_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0




theorem _root_.D1Bound5.smallPairPilotTraceZeroNoTriangle_41_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_2 smallPairPilotLarge_41 = true := by sorry

end D1Bound5
end
