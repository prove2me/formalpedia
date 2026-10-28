-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared43_left_checked
-- name    : D1Bound5.PairLightPrepared43.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:37.194986+00:00
-- url     : https://prove2.me/theorems/501c8871-8284-4df8-9a32-60a2a1320c42
-- title:
--   Pair Light Prepared43 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared43.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly43.lean, lines 24-29, SHA-256 a1f93b85259f267bea1466e442343da00fa48b8f5128ef4939b965627b146f42. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs43_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_3_Definitions

section
namespace D1Bound5.PairLightPrepared43
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared43.left_checked :
    pairIndependentBool smallPairSieve_1_3 (pairSplitByMask smallPairLarge_43 PairGraphPrepared43.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared43
end
