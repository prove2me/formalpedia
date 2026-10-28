-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared48_leftVertices_eq
-- name    : D1Bound5.PairLightPrepared48.leftVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:16:18.868989+00:00
-- url     : https://prove2.me/theorems/2d1a6b26-7cb3-4b48-bc1e-5c9e4ab415e0
-- title:
--   Pair Light Prepared48 — left Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared48.leftVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly48.lean, lines 13-15, SHA-256 cbece2e752376f1748b5f5e76f355572d81d9117b4233dcc85b4e0f49ce687fe. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData48Left_Definitions_001

section
namespace D1Bound5.PairLightPrepared48
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared48.leftVertices_eq :
    leftVertices = (pairSplitByMask smallPairLarge_48 PairGraphPrepared48.colors).1.map pairLightCoordinates := by sorry















end D1Bound5.PairLightPrepared48
end
