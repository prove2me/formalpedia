-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared35_leftVertices_eq
-- name    : D1Bound5.PairLightPrepared35.leftVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:23:38.305994+00:00
-- url     : https://prove2.me/theorems/1d1133e1-4b80-4bfb-8ce1-33176bc29a0c
-- title:
--   Pair Light Prepared35 — left Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared35.leftVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly35.lean, lines 13-15, SHA-256 16e0eab6b5beded14cffd88925033079f639e43f217ee23546e34b32728bbc42. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData35Left_Definitions_001

section
namespace D1Bound5.PairLightPrepared35
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared35.leftVertices_eq :
    leftVertices = (pairSplitByMask smallPairLarge_35 PairGraphPrepared35.colors).1.map pairLightCoordinates := by sorry















end D1Bound5.PairLightPrepared35
end
