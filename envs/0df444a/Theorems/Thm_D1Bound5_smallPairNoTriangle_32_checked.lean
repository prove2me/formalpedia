-- Prove2me | Theorems.Thm_D1Bound5_smallPairNoTriangle_32_checked
-- name    : D1Bound5.smallPairNoTriangle_32_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:00.942522+00:00
-- url     : https://prove2.me/theorems/090bac2c-6a18-4311-910e-6990ea25ee95
-- title:
--   Small Pair No Triangle 32 checked
-- statement:
--   Auxiliary result `smallPairNoTriangle_32_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphTriangle32.lean, lines 13-17, SHA-256 690f85bc066eb0817f5e7eac1fdc67eaa4dffaac85c1fea15bfddc8b4808010a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs32_Definitions
import Definitions.Def_D1Bound5_SmallPairSieve_0_6_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairNoTriangle_32_checked :
    pairGraphTriangleFreeBool smallPairSieve_0_6 smallPairLarge_32 = true := by sorry

end D1Bound5
end
