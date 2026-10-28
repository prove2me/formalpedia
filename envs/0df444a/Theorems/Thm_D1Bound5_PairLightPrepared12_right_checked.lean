-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared12_right_checked
-- name    : D1Bound5.PairLightPrepared12.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:04.773718+00:00
-- url     : https://prove2.me/theorems/26f0ee89-dc9c-4faa-b8da-1e956c4c9fca
-- title:
--   Pair Light Prepared12 — right checked
-- statement:
--   Auxiliary result `PairLightPrepared12.right_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly12.lean, lines 42-47, SHA-256 f97804cda6000ca5224866d4c03f9dac3bc3dfdcf5a143f857e57e3150616c7e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.List.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairBipartiteCheck_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs12_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5.PairLightPrepared12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

















theorem _root_.D1Bound5.PairLightPrepared12.right_checked :
    pairIndependentBool smallPairSieve_0_1 (pairSplitByMask smallPairLarge_12 PairGraphPrepared12.colors).2 = true := by sorry

end D1Bound5.PairLightPrepared12
end
