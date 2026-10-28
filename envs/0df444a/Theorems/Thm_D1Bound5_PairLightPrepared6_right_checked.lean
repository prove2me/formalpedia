-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared6_right_checked
-- name    : D1Bound5.PairLightPrepared6.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:59.63002+00:00
-- url     : https://prove2.me/theorems/efc2f5d1-0df5-4fdb-81e8-1f5fb0e2430c
-- title:
--   Pair Light Prepared6 — right checked
-- statement:
--   Auxiliary result `PairLightPrepared6.right_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly6.lean, lines 42-47, SHA-256 bca8453210349e854ee98813aa1f5b360d0b8dedde6c310cf2e2d40cd35adaec. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs6_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5.PairLightPrepared6
set_option maxRecDepth 100000
set_option maxHeartbeats 0

















theorem _root_.D1Bound5.PairLightPrepared6.right_checked :
    pairIndependentBool smallPairSieve_0_1 (pairSplitByMask smallPairLarge_6 PairGraphPrepared6.colors).2 = true := by sorry

end D1Bound5.PairLightPrepared6
end
