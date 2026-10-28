-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared15_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared15.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:15:33.500857+00:00
-- url     : https://prove2.me/theorems/3700329b-db48-4f17-9daf-400f6adbe4e7
-- title:
--   Pair Light Prepared15 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared15.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly15.lean, lines 31-33, SHA-256 04ada0753389d6f43d271fa3acd322df3dd861717571a4b08da8705effee1c54. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData15RightVertices_Definitions

section
namespace D1Bound5.PairLightPrepared15
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared15.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_15 PairGraphPrepared15.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared15
end
