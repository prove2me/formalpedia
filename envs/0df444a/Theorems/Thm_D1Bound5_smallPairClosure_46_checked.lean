-- Prove2me | Theorems.Thm_D1Bound5_smallPairClosure_46_checked
-- name    : D1Bound5.smallPairClosure_46_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:34.96191+00:00
-- url     : https://prove2.me/theorems/8a9bc3ff-4557-425b-a08a-fa1d428cba8e
-- title:
--   Small Pair Closure 46 checked
-- statement:
--   Auxiliary result `smallPairClosure_46_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphClosure46.lean, lines 104-108, SHA-256 6056b2f3c92c747b1c642de914093c1a45e0bf52524cd2c571fb9d9b281c9c7c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs46_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

open PairGraphPrepared46



theorem _root_.D1Bound5.smallPairClosure_46_checked :
    pairClosureBool smallPairA_46 smallPairB_46
      (10^1100) smallPairClosure_46 = true := by sorry

end D1Bound5
end
