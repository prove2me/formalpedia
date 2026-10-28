-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_1_checked
-- name    : D1Bound5.smallPairSeeds_1_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:58.347655+00:00
-- url     : https://prove2.me/theorems/05fe62fc-723d-40a1-9f38-38723dda834a
-- title:
--   Small Pair Seeds 1 checked
-- statement:
--   Auxiliary result `smallPairSeeds_1_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic1.lean, lines 8-11, SHA-256 4cf70ea7f533f7bcf9c1290bafbe049be2d7c2be79e22d2ce03e1d504275229c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs1_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_1_checked :
    pairSeedsCoveredBool smallPairA_1 smallPairB_1
      seedRootDisk_0_1 smallPairClosure_1 = true := by sorry





end D1Bound5
end
