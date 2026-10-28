-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_22_checked
-- name    : D1Bound5.smallPairSeeds_22_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:28:21.553872+00:00
-- url     : https://prove2.me/theorems/4aa311fc-3618-409f-a136-8aa241c3540f
-- title:
--   Small Pair Seeds 22 checked
-- statement:
--   Auxiliary result `smallPairSeeds_22_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic22.lean, lines 9-12, SHA-256 adb0922d008fd88dc4e6c502403fa271eff76e18e3492f2421c3a144fe6a9dcf. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs22_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_22_checked :
    pairSeedsCoveredBool smallPairA_22 smallPairB_22
      seedRootDisk_1_1 smallPairClosure_22 = true := by sorry





end D1Bound5
end
