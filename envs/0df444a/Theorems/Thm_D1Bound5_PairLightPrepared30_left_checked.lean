-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared30_left_checked
-- name    : D1Bound5.PairLightPrepared30.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:14.228993+00:00
-- url     : https://prove2.me/theorems/7e8bc2a3-ab6f-4666-bec2-499769624298
-- title:
--   Pair Light Prepared30 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared30.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly30.lean, lines 24-29, SHA-256 d3e271a46210b697f08a25cf096f1dd3e031fd5faa932a54c831d00cc7dbd661. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_003
import Definitions.Def_D1Bound5_SmallPairGraphInputs30_Definitions_004
import Definitions.Def_D1Bound5_SmallPairSieve_1_1_Definitions

section
namespace D1Bound5.PairLightPrepared30
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared30.left_checked :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_30 PairGraphPrepared30.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared30
end
