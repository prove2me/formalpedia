-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_48_checked
-- name    : D1Bound5.smallPairFilter_48_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:55.683923+00:00
-- url     : https://prove2.me/theorems/b30bc903-d9d7-4076-b498-db3899327450
-- title:
--   Small Pair Filter 48 checked
-- statement:
--   Auxiliary result `smallPairFilter_48_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic48.lean, lines 13-15, SHA-256 e6244101e338a3e2941a187afc7d87015a68a1d81020bdd3e34df785c575e237. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs48_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_48_checked :
    largePairVertices smallPairA_48 smallPairB_48 smallPairClosure_48 = smallPairLarge_48 := by sorry



end D1Bound5
end
