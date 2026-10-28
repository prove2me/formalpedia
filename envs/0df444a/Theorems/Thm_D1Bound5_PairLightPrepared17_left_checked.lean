-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared17_left_checked
-- name    : D1Bound5.PairLightPrepared17.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:51.663736+00:00
-- url     : https://prove2.me/theorems/f717962f-201f-4c59-acd7-7298c12018c4
-- title:
--   Pair Light Prepared17 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared17.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly17.lean, lines 24-29, SHA-256 4a4c3cceb1e234d5a7ca9081233a76921a24091b498fb613e4d351fee3c72181. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs17_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_0_2_Definitions

section
namespace D1Bound5.PairLightPrepared17
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared17.left_checked :
    pairIndependentBool smallPairSieve_0_2 (pairSplitByMask smallPairLarge_17 PairGraphPrepared17.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared17
end
