-- Prove2me | Theorems.Thm_D1Bound5_smallPairFilter_15_checked
-- name    : D1Bound5.smallPairFilter_15_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:20.332839+00:00
-- url     : https://prove2.me/theorems/7466629e-af9a-4f10-9c5c-adf9bdd4978e
-- title:
--   Small Pair Filter 15 checked
-- statement:
--   Auxiliary result `smallPairFilter_15_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic15.lean, lines 13-15, SHA-256 27956ff83c44edcf021124046f7b22ee8393f7d95ac6d4f44c943afd05ced6a4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_002
import Definitions.Def_D1Bound5_SmallPairGraphInputs15_Definitions_003

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0



theorem _root_.D1Bound5.smallPairFilter_15_checked :
    largePairVertices smallPairA_15 smallPairB_15 smallPairClosure_15 = smallPairLarge_15 := by sorry



end D1Bound5
end
