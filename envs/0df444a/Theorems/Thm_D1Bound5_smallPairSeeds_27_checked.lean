-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_27_checked
-- name    : D1Bound5.smallPairSeeds_27_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:25:03.057504+00:00
-- url     : https://prove2.me/theorems/c8ebee7a-c725-4104-8f59-c138683681b2
-- title:
--   Small Pair Seeds 27 checked
-- statement:
--   Auxiliary result `smallPairSeeds_27_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic27.lean, lines 9-12, SHA-256 399818bc674ca081e08a5f91d4f63a18326234fecd9182d863ffe24f60a0a63e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs27_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_27_checked :
    pairSeedsCoveredBool smallPairA_27 smallPairB_27
      seedRootDisk_1_1 smallPairClosure_27 = true := by sorry





end D1Bound5
end
