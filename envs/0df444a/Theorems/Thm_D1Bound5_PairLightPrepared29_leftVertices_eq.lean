-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared29_leftVertices_eq
-- name    : D1Bound5.PairLightPrepared29.leftVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:13:28.680548+00:00
-- url     : https://prove2.me/theorems/dddde84f-b4c0-4e2f-bfd9-5d87de00a98b
-- title:
--   Pair Light Prepared29 — left Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared29.leftVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly29.lean, lines 13-15, SHA-256 dbacc8a2310d456f91b493fad40c48e58201b13c3a10f48ba7591cc4e9cbc81f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_004
import Definitions.Def_D1Bound5_SmallPairLightData29Left_Definitions_001

section
namespace D1Bound5.PairLightPrepared29
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared29.leftVertices_eq :
    leftVertices = (pairSplitByMask smallPairLarge_29 PairGraphPrepared29.colors).1.map pairLightCoordinates := by sorry















end D1Bound5.PairLightPrepared29
end
