-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_40_checked
-- name    : D1Bound5.smallPairClosure_40_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:49.513032+00:00
-- url     : https://prove2.me/theorems/13260b3d-dd9b-473a-a47e-2c63ea17403b
-- title:
--   Small Pair Closure 40 checked
-- statement:
--   Auxiliary result `smallPairClosure_40_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure40.lean, lines 74-78, SHA-256 011ef435ec747fb28ab334ae19fdc565fab86c68e1274439ac90eba2ffb7b196. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs40_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared40



theorem _root_.D1Bound5.smallPairClosure_40_checked :
    pairClosureBool smallPairA_40 smallPairB_40
      (10^1100) smallPairClosure_40 = true := by sorry

end D1Bound5
end
