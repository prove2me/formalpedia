-- Prove2me | Theorems.Thm_D1Bound5_smallPairPilotAllTraceZero_41_checked
-- name    : D1Bound5.smallPairPilotAllTraceZero_41_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:56:55.75+00:00
-- url     : https://prove2.me/theorems/659e99c7-ce43-4ddb-90bd-f79eac9dca28
-- title:
--   Small Pair Pilot All Trace Zero 41 checked
-- statement:
--   Every original large vertex is checked once. This is the exact frozen 372-entry list; no pair, color or coordinate is omitted or replaced.
-- source:
--   D1Bound5/SmallPairTraceZeroPilot41.lean, lines 9-13, SHA-256 5873e50be7d81103b7dc1e77ba68f8e8b774645e2c18a7075508d07bfc9ad4c6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairGraphNoThreeTransfer_Definitions
import Definitions.Def_D1Bound5_SmallPairBipartitePilotData41_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0


theorem _root_.D1Bound5.smallPairPilotAllTraceZero_41_checked :
    pairAllTraceZeroBool smallPairPilotLarge_41 = true := by sorry



end D1Bound5
end
