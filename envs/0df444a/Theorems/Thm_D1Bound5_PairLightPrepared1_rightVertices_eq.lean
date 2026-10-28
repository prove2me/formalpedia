-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared1_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared1.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:14:50.289764+00:00
-- url     : https://prove2.me/theorems/1222b63f-d25a-46fc-8428-32dbb24764b8
-- title:
--   Pair Light Prepared1 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared1.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly1.lean, lines 31-33, SHA-256 aa4d0f7e0c25b110a19624502dedc5a05c11705261bb7992594a13587facbf72. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs1_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData1Right_Definitions_001

section
namespace D1Bound5.PairLightPrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared1.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_1 PairGraphPrepared1.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared1
end
