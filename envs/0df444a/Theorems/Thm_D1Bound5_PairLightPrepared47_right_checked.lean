-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared47_right_checked
-- name    : D1Bound5.PairLightPrepared47.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:29:56.089987+00:00
-- url     : https://prove2.me/theorems/8d93d943-7f5f-44b0-ab23-e25eab38839d
-- title:
--   Pair Light Prepared47 — right checked
-- statement:
--   Auxiliary result `PairLightPrepared47.right_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly47.lean, lines 42-47, SHA-256 f6a171b324aab343a87dce66e76db94cd8d9d029fdf2a63b2f0ffc3a7537664a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs47_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_1_6_Definitions

section
namespace D1Bound5.PairLightPrepared47
set_option maxRecDepth 100000
set_option maxHeartbeats 0

















theorem _root_.D1Bound5.PairLightPrepared47.right_checked :
    pairIndependentBool smallPairSieve_1_6 (pairSplitByMask smallPairLarge_47 PairGraphPrepared47.colors).2 = true := by sorry

end D1Bound5.PairLightPrepared47
end
