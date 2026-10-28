-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_46_checked
-- name    : D1Bound5.smallPairSeeds_46_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:24:52.421773+00:00
-- url     : https://prove2.me/theorems/4a054ea9-29eb-4ca7-a730-bafb8d18aa9d
-- title:
--   Small Pair Seeds 46 checked
-- statement:
--   Auxiliary result `smallPairSeeds_46_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic46.lean, lines 8-11, SHA-256 f9a32640a9b051fd190da9bbb41a14d597818d62631e660bf974bcf2f782f93c. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs46_Definitions_001
import Definitions.Def_D1Bound5_TwoSmallSeedDisks_Definitions

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_46_checked :
    pairSeedsCoveredBool smallPairA_46 smallPairB_46
      seedRootDisk_1_6 smallPairClosure_46 = true := by sorry





end D1Bound5
end
