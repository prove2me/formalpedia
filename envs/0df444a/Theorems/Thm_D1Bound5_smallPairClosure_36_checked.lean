-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_36_checked
-- name    : D1Bound5.smallPairClosure_36_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:24:57.901907+00:00
-- url     : https://prove2.me/theorems/9ea1311a-4aea-4bf8-89a1-faa9658facee
-- title:
--   Small Pair Closure 36 checked
-- statement:
--   Auxiliary result `smallPairClosure_36_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure36.lean, lines 13-17, SHA-256 084b9f4905e8f5f186ef6ba942fc72e303620b09e7e489862dedf6510b93330e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared36



theorem _root_.D1Bound5.smallPairClosure_36_checked :
    pairClosureBool smallPairA_36 smallPairB_36
      (10^1100) smallPairClosure_36 = true := by sorry

end D1Bound5
end
