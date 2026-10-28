-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared10_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared10.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:15:49.839483+00:00
-- url     : https://prove2.me/theorems/dce998a7-ddf3-45d2-9a69-e143363ea8de
-- title:
--   Pair Light Prepared10 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared10.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly10.lean, lines 31-33, SHA-256 3d07cf877db3c8212cedaa2cc9c8e0a6e753987e92bdb9e6eddd659ad00b96de. Project: https://github.com/tomislav-math/d1-bound5-lean

import Init
import Mathlib.Algebra.Order.Ring.Abs
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
import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_PairLightArithmeticBridge_Definitions
import Definitions.Def_D1Bound5_PairLightArithmetic_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs10_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData10RightVertices_Definitions

section
namespace D1Bound5.PairLightPrepared10
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared10.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_10 PairGraphPrepared10.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared10
end
