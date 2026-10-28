-- Prove2me | Theorems.Thm_D1Bound5_smallPairNoTriangle_37_checked
-- name    : D1Bound5.smallPairNoTriangle_37_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:08.81284+00:00
-- url     : https://prove2.me/theorems/fffac5ec-5db4-454e-9013-91aec21dd33b
-- title:
--   Small Pair No Triangle 37 checked
-- statement:
--   Auxiliary result `smallPairNoTriangle_37_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphTriangle37.lean, lines 13-17, SHA-256 83c52ca82dffbb6e620c5ebbfe9a207409c223b81ecc80fd1de8bd0e8709fa5c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_003
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairNoTriangle_37_checked :
    pairGraphTriangleFreeBool smallPairSieve_1_2 smallPairLarge_37 = true := by sorry

end D1Bound5
end
