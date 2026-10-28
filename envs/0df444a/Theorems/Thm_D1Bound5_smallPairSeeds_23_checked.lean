-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_23_checked
-- name    : D1Bound5.smallPairSeeds_23_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:17.630683+00:00
-- url     : https://prove2.me/theorems/79c568c7-725a-4647-9297-921f2cea021f
-- title:
--   Small Pair Seeds 23 checked
-- statement:
--   Auxiliary result `smallPairSeeds_23_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic23.lean, lines 8-11, SHA-256 d47f8b0d8d49e0e0787d22d1aed13b248a747a1f313b9f5d1702b98a913fd3fb. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs23_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_23_checked :
    pairSeedsCoveredBool smallPairA_23 smallPairB_23
      seedRootDisk_1_1 smallPairClosure_23 = true := by sorry





end D1Bound5
end
