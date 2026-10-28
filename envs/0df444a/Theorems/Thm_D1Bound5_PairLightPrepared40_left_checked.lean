-- Prove2me | Theorems.Thm_D1Bound5_PairLightPrepared40_left_checked
-- name    : D1Bound5.PairLightPrepared40.left_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:30:00.364824+00:00
-- url     : https://prove2.me/theorems/2397d474-51da-453a-877d-9f8feba9c104
-- title:
--   Pair Light Prepared40 — left checked
-- statement:
--   Auxiliary result `PairLightPrepared40.left_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairLightAssembly40.lean, lines 24-29, SHA-256 de2977aaf1d1060731b47fcba8ff254e81d16c036949fd4791d5fedfc46176c6. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs40_Definitions_002
import Definitions.Def_D1Bound5_SmallPairSieve_1_2_Definitions

section
namespace D1Bound5.PairLightPrepared40
set_option maxRecDepth 100000
set_option maxHeartbeats 0









theorem _root_.D1Bound5.PairLightPrepared40.left_checked :
    pairIndependentBool smallPairSieve_1_2 (pairSplitByMask smallPairLarge_40 PairGraphPrepared40.colors).1 = true := by sorry









end D1Bound5.PairLightPrepared40
end
