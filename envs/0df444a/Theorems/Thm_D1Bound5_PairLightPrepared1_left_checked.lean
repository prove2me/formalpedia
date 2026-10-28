-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared1_left_checked
-- name    : D1Bound5.PairLightPrepared1.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:56.230151+00:00
-- url     : https://prove2.me/theorems/591dbb60-4ab3-4b09-8c38-2f07e7dad347
-- title:
--   Pair Light Prepared1 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared1.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly1.lean, lines 24-29, SHA-256 aa4d0f7e0c25b110a19624502dedc5a05c11705261bb7992594a13587facbf72. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs1_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_0_1_Definitions

section
namespace D1Bound5.PairLightPrepared1
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared1.left_checked :
    pairIndependentBool smallPairSieve_0_1 (pairSplitByMask smallPairLarge_1 PairGraphPrepared1.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared1
end
