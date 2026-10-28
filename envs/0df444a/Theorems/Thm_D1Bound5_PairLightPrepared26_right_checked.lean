-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared26_right_checked
-- name    : D1Bound5.PairLightPrepared26.right_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:32:02.235614+00:00
-- url     : https://prove2.me/theorems/01791a73-86b0-46f4-9f36-a941d3a34315
-- title:
--   Pair Light Prepared26 — right checked
-- statement:
--   Auxiliary result `PairLightPrepared26.right_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly26.lean, lines 45-50, SHA-256 9d96afc74fd9d232ca974725450b1fcadaee3e9cc9c912d500a5ef6761bcba9c. Project: https://github.com/tomislav-math/d1-bound5-lean

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

















theorem _root_.D1Bound5.PairLightPrepared26.right_checked :
    pairIndependentBool smallPairSieve_1_1 (pairSplitByMask smallPairLarge_26 PairGraphPrepared26.colors).2 = true := by sorry

end D1Bound5.PairLightPrepared26
end
