-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared19_right_checked
-- name    : D1Bound5.PairLightPrepared19.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:18.215124+00:00
-- url     : https://prove2.me/theorems/61e0b4db-afc1-45b1-b3ba-b306447ea7b7
-- title:
--   Pair Light Prepared19 — right checked
-- statement:
--   Auxiliary result `PairLightPrepared19.right_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly19.lean, lines 42-47, SHA-256 aea09e532976f10a3d1c124342265753300684790ab29aaa3e4efcb0253d24b1. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5.PairLightPrepared19
set_option maxRecDepth 100000
set_option maxHeartbeats 0

















theorem _root_.D1Bound5.PairLightPrepared19.right_checked :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_19 PairGraphPrepared19.colors).2 = true := by sorry

end D1Bound5.PairLightPrepared19
end
