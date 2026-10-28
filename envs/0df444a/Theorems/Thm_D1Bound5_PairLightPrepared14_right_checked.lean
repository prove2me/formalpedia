-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared14_right_checked
-- name    : D1Bound5.PairLightPrepared14.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:29:58.44114+00:00
-- url     : https://prove2.me/theorems/f2808fdd-723b-4200-894a-9239d241dd06
-- title:
--   Pair Light Prepared14 — right checked
-- statement:
--   Auxiliary result `PairLightPrepared14.right_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly14.lean, lines 42-47, SHA-256 8e04fa21749760833311156b742b4d2523d0772272f9c254e49d6ff74ddf3eae. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs14_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions

section
namespace D1Bound5.PairLightPrepared14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

















theorem _root_.D1Bound5.PairLightPrepared14.right_checked :
    pairIndependentBool smallPairSieve_0_2 (pairSplitByMask smallPairLarge_14 PairGraphPrepared14.colors).2 = true := by sorry

end D1Bound5.PairLightPrepared14
end
