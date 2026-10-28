-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared26_left_checked
-- name    : D1Bound5.PairLightPrepared26.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:27.308984+00:00
-- url     : https://prove2.me/theorems/49f4d366-b9e4-4baf-94e2-ba9c97b1e5d1
-- title:
--   Pair Light Prepared26 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared26.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly26.lean, lines 27-32, SHA-256 9d96afc74fd9d232ca974725450b1fcadaee3e9cc9c912d500a5ef6761bcba9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs26_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5.PairLightPrepared26
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared26.left_checked :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_26 PairGraphPrepared26.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared26
end
