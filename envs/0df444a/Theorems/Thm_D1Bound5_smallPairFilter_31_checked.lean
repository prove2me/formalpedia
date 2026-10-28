-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_31_checked
-- name    : D1Bound5.smallPairFilter_31_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:31.634018+00:00
-- url     : https://prove2.me/theorems/18739610-1879-44b5-a39b-08e0ff497032
-- title:
--   Small Pair Filter 31 checked
-- statement:
--   Auxiliary result `smallPairFilter_31_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic31.lean, lines 14-16, SHA-256 1a7c88f2e5e6b6327f3a5b127183b65db23615cebc216ac91176801db6b20d2f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_31_checked :
    largePairVertices smallPairA_31 smallPairB_31 smallPairClosure_31 = smallPairLarge_31 := by sorry



end D1Bound5
end
