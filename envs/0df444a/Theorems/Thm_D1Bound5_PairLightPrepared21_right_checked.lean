-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared21_right_checked
-- name    : D1Bound5.PairLightPrepared21.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:13.320663+00:00
-- url     : https://prove2.me/theorems/edd98ce6-9f0c-4832-b396-50b3cf9d45d6
-- title:
--   Pair Light Prepared21 — right checked
-- statement:
--   Auxiliary result `PairLightPrepared21.right_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly21.lean, lines 42-47, SHA-256 d0ca2f84556f020d1c9db6187a48573f87857819e7c7ebd49a60cf1ab9e33cae. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs21_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5.PairLightPrepared21
set_option maxRecDepth 100000
set_option maxHeartbeats 0

















theorem _root_.D1Bound5.PairLightPrepared21.right_checked :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_21 PairGraphPrepared21.colors).2 = true := by sorry

end D1Bound5.PairLightPrepared21
end
