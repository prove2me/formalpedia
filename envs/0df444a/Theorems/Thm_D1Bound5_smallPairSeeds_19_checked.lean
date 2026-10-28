-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_19_checked
-- name    : D1Bound5.smallPairSeeds_19_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:26:23.472195+00:00
-- url     : https://prove2.me/theorems/c303d0e0-6a17-4d20-8bb5-f48b6812d42b
-- title:
--   Small Pair Seeds 19 checked
-- statement:
--   Auxiliary result `smallPairSeeds_19_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic19.lean, lines 8-11, SHA-256 3b56e51ec5eabd27d405632f3d20cd07766a573c3ca28f4252e17239730adc09. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs19_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_19_checked :
    pairSeedsCoveredBool smallPairA_19 smallPairB_19
      seedRootDisk_1_1 smallPairClosure_19 = true := by sorry





end D1Bound5
end
