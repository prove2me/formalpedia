-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared3_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared3.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:14:56.414025+00:00
-- url     : https://prove2.me/theorems/54b681f4-742e-4d1d-a388-2bbd7c5eda34
-- title:
--   Pair Light Prepared3 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared3.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly3.lean, lines 31-33, SHA-256 56edac3dc1067d6b0f3c0222e535e97bb79b045082fc27258c676fd28249c84d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs3_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData3RightVertices_Definitions

section
namespace D1Bound5.PairLightPrepared3
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared3.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_3 PairGraphPrepared3.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared3
end
