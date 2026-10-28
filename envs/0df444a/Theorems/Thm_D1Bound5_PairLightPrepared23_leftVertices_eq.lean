-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared23_leftVertices_eq
-- name    : D1Bound5.PairLightPrepared23.leftVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:30:04.147315+00:00
-- url     : https://prove2.me/theorems/8d22c476-dca5-41da-a911-ffdfab7ae169
-- title:
--   Pair Light Prepared23 — left Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared23.leftVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly23.lean, lines 13-15, SHA-256 84f5e74de18d4bc2855ddcc344172c33d1f5954d20968997ebb86b3b83f0e486. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData23LeftVertices_Definitions

section
namespace D1Bound5.PairLightPrepared23
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared23.leftVertices_eq :
    leftVertices = (pairSplitByMask smallPairLarge_23 PairGraphPrepared23.colors).1.map pairLightCoordinates := by sorry















end D1Bound5.PairLightPrepared23
end
