-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared46_leftVertices_eq
-- name    : D1Bound5.PairLightPrepared46.leftVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:13:28.492181+00:00
-- url     : https://prove2.me/theorems/ebb15d89-adfe-4632-b01e-bfa114cec11b
-- title:
--   Pair Light Prepared46 — left Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared46.leftVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly46.lean, lines 13-15, SHA-256 6e234132c97201897fc0a7fb8b6edd79e6ed62c8792a7bf0786831c44ea7aefb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs46_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData46Left_Definitions_001

section
namespace D1Bound5.PairLightPrepared46
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.PairLightPrepared46.leftVertices_eq :
    leftVertices = (pairSplitByMask smallPairLarge_46 PairGraphPrepared46.colors).1.map pairLightCoordinates := by sorry















end D1Bound5.PairLightPrepared46
end
