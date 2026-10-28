-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_24_checked
-- name    : D1Bound5.smallPairSeeds_24_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:33.289424+00:00
-- url     : https://prove2.me/theorems/734849d6-80cb-4b60-bf6e-6c3fe41accf9
-- title:
--   Small Pair Seeds 24 checked
-- statement:
--   Auxiliary result `smallPairSeeds_24_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic24.lean, lines 8-11, SHA-256 7455bd6044ae044909b79f11651e5bc1422eca78a814090097ef6fa1c60abaf0. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs24_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_24_checked :
    pairSeedsCoveredBool smallPairA_24 smallPairB_24
      seedRootDisk_1_1 smallPairClosure_24 = true := by sorry





end D1Bound5
end
