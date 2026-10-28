-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_39_checked
-- name    : D1Bound5.smallPairSeeds_39_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:20.139956+00:00
-- url     : https://prove2.me/theorems/8fbba4a8-1475-47f4-800b-055c9c2e18df
-- title:
--   Small Pair Seeds 39 checked
-- statement:
--   Auxiliary result `smallPairSeeds_39_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic39.lean, lines 8-11, SHA-256 b31dee9314b58b7e1aa4f8295deb3f5469a078126ebe0065fab4650a4c915254. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Mathlib.Data.List.Range
import Mathlib.Data.ZMod.Basic
import Mathlib.LinearAlgebra.Dimension.Free
import Mathlib.NumberTheory.NumberField.InfinitePlace.TotallyRealComplex
import Mathlib.NumberTheory.NumberField.Norm
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs39_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_39_checked :
    pairSeedsCoveredBool smallPairA_39 smallPairB_39
      seedRootDisk_1_2 smallPairClosure_39 = true := by sorry





end D1Bound5
end
