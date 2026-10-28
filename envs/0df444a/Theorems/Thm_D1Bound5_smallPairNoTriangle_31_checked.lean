-- Prove2me | Theorems.Thm_D1Bound5_smallPairNoTriangle_31_checked
-- name    : D1Bound5.smallPairNoTriangle_31_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:08.79569+00:00
-- url     : https://prove2.me/theorems/9e60b938-1210-40bc-ad81-08b4ce49cd99
-- title:
--   Small Pair No Triangle 31 checked
-- statement:
--   Auxiliary result `smallPairNoTriangle_31_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphTriangle31.lean, lines 13-17, SHA-256 a206463f9ff12debd40c88e6a83a850e9f3b508578f175b748ce63c018e9df0d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs31_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_5_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairNoTriangle_31_checked :
    pairGraphTriangleFreeBool smallPairSieve_0_5 smallPairLarge_31 = true := by sorry

end D1Bound5
end
