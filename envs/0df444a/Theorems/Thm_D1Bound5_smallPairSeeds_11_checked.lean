-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_11_checked
-- name    : D1Bound5.smallPairSeeds_11_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:50:27.611772+00:00
-- url     : https://prove2.me/theorems/a6941e51-64b3-4d3e-b97c-0356ef03f8c7
-- title:
--   Small Pair Seeds 11 checked
-- statement:
--   Auxiliary result `smallPairSeeds_11_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic11.lean, lines 8-11, SHA-256 364875a34ed5bd9637ca968a549dadc1fb5a5e775dc46c04000fe048f6339b2e. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs11_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_11_checked :
    pairSeedsCoveredBool smallPairA_11 smallPairB_11
      seedRootDisk_0_1 smallPairClosure_11 = true := by sorry





end D1Bound5
end
