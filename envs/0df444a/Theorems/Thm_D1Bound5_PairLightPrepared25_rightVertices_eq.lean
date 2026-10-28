-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared25_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared25.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:27:09.925167+00:00
-- url     : https://prove2.me/theorems/921864fa-d8c0-4e27-ba06-03cc7f196d34
-- title:
--   Pair Light Prepared25 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared25.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly25.lean, lines 31-33, SHA-256 bd192e00e2176c523d859addb25c5bf30a7494b725c17168d6f36a58f7031fa6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs25_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData25Right_Definitions_001

section
namespace D1Bound5.PairLightPrepared25
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared25.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_25 PairGraphPrepared25.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared25
end
