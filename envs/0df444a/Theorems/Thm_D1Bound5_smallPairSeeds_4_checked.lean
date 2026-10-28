-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_4_checked
-- name    : D1Bound5.smallPairSeeds_4_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:22:55.878841+00:00
-- url     : https://prove2.me/theorems/5491508e-15e5-4793-850a-dfd27a7ccf73
-- title:
--   Small Pair Seeds 4 checked
-- statement:
--   Auxiliary result `smallPairSeeds_4_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic4.lean, lines 8-11, SHA-256 26f94cc1e16460b2860a9b8697ad175676e20a8f0446ea9a20e3657aa2bf6817. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs4_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_4_checked :
    pairSeedsCoveredBool smallPairA_4 smallPairB_4
      seedRootDisk_0_1 smallPairClosure_4 = true := by sorry





end D1Bound5
end
