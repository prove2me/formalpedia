-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_11_checked
-- name    : D1Bound5.smallPairClosure_11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:51.275431+00:00
-- url     : https://prove2.me/theorems/5bf6b920-a833-426c-b7e4-aaa49ba3269e
-- title:
--   Small Pair Closure 11 checked
-- statement:
--   Auxiliary result `smallPairClosure_11_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure11.lean, lines 104-108, SHA-256 07e7bbd6da02ee4d9003fa0926ed74dead2a79cca9a0031f674b2e1ed3ba933a. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs11_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared11



theorem _root_.D1Bound5.smallPairClosure_11_checked :
    pairClosureBool smallPairA_11 smallPairB_11
      (10^1100) smallPairClosure_11 = true := by sorry

end D1Bound5
end
