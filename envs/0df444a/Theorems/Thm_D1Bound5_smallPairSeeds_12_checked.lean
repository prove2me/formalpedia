-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_12_checked
-- name    : D1Bound5.smallPairSeeds_12_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:52:40.641772+00:00
-- url     : https://prove2.me/theorems/1651ea74-811f-4dc5-8642-55b2e10c31c2
-- title:
--   Small Pair Seeds 12 checked
-- statement:
--   Auxiliary result `smallPairSeeds_12_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic12.lean, lines 8-11, SHA-256 f63837b55c69bdb709897de72e83d4ac38d1ee00669f9ffa16acb6f62232a866. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs12_Definitions_001

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_12_checked :
    pairSeedsCoveredBool smallPairA_12 smallPairB_12
      seedRootDisk_0_1 smallPairClosure_12 = true := by sorry





end D1Bound5
end
