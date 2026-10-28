-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared47_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared47.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:15:05.17717+00:00
-- url     : https://prove2.me/theorems/8ee844f0-a9d0-45f1-87c8-902008648dd0
-- title:
--   Pair Light Prepared47 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared47.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly47.lean, lines 31-33, SHA-256 f6a171b324aab343a87dce66e76db94cd8d9d029fdf2a63b2f0ffc3a7537664a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs47_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData47_Definitions_003

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared47.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_47 PairGraphPrepared47.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared47
end
