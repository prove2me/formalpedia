-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_29_checked
-- name    : D1Bound5.smallPairClosure_29_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:25:06.576331+00:00
-- url     : https://prove2.me/theorems/9cb7886a-28d5-478e-85e0-0ac7263499cd
-- title:
--   Small Pair Closure 29 checked
-- statement:
--   Auxiliary result `smallPairClosure_29_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure29.lean, lines 104-108, SHA-256 a02d88faf9018c992ccf9ce71905532ce94578632d12e96ecd5c414abb4d62fc. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs29_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared29



theorem _root_.D1Bound5.smallPairClosure_29_checked :
    pairClosureBool smallPairA_29 smallPairB_29
      (10^1100) smallPairClosure_29 = true := by sorry

end D1Bound5
end
