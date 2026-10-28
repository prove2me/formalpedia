-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared4_left_checked
-- name    : D1Bound5.PairLightPrepared4.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:31:15.104642+00:00
-- url     : https://prove2.me/theorems/fe8a150f-b364-48e8-aa04-58d1356af49a
-- title:
--   Pair Light Prepared4 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared4.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly4.lean, lines 24-29, SHA-256 a33d4d40649da2331bd8a9202b6f96f06e58f1b224932a9a23787556c880875f. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5.PairLightPrepared4
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared4.left_checked :
    pairIndependentBool smallPairSieve_0_1 (pairSplitByMask smallPairLarge_4 PairGraphPrepared4.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared4
end
