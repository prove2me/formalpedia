-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_37_checked
-- name    : D1Bound5.smallPairSeeds_37_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:44.649518+00:00
-- url     : https://prove2.me/theorems/ccc052d9-17bd-4163-a6c0-8a0ab613b9e7
-- title:
--   Small Pair Seeds 37 checked
-- statement:
--   Auxiliary result `smallPairSeeds_37_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic37.lean, lines 9-12, SHA-256 7261cda8270070eae87a83e46a05e8dfdd9d47ce64647c0cd5b58d0edc9f00a4. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs37_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_37_checked :
    pairSeedsCoveredBool smallPairA_37 smallPairB_37
      seedRootDisk_1_2 smallPairClosure_37 = true := by sorry





end D1Bound5
end
