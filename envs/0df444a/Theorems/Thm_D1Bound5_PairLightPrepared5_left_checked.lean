-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared5_left_checked
-- name    : D1Bound5.PairLightPrepared5.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:22.900163+00:00
-- url     : https://prove2.me/theorems/2f00de68-b984-4c04-9780-07ab85524be2
-- title:
--   Pair Light Prepared5 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared5.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly5.lean, lines 24-29, SHA-256 3040aaa1038e59a2ab708ae9b5d6455e78149d1c25343b2073fd56134918c6f8. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs5_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5.PairLightPrepared5
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared5.left_checked :
    pairIndependentBool smallPairSieve_0_1 (pairSplitByMask smallPairLarge_5 PairGraphPrepared5.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared5
end
