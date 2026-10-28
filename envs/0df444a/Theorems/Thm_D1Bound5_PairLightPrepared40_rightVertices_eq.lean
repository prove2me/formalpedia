-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared40_rightVertices_eq
-- name    : D1Bound5.PairLightPrepared40.rightVertices_eq
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T02:13:59.001022+00:00
-- url     : https://prove2.me/theorems/256405d8-addf-4c00-a363-4ea303213de9
-- title:
--   Pair Light Prepared40 — right Vertices eq
-- statement:
--   Auxiliary result `PairLightPrepared40.rightVertices_eq` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly40.lean, lines 31-33, SHA-256 de2977aaf1d1060731b47fcba8ff254e81d16c036949fd4791d5fedfc46176c6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs40_Definitions_002
import Definitions.Def_D1Bound5_SmallPairLightData40_Definitions_003

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0











theorem _root_.D1Bound5.PairLightPrepared40.rightVertices_eq :
    rightVertices = (pairSplitByMask smallPairLarge_40 PairGraphPrepared40.colors).2.map pairLightCoordinates := by sorry







end D1Bound5.PairLightPrepared40
end
