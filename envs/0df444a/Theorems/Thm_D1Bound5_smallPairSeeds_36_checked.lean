-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_36_checked
-- name    : D1Bound5.smallPairSeeds_36_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:25:22.710609+00:00
-- url     : https://prove2.me/theorems/1f200cd5-16b9-4031-87fb-63d1dbe11c05
-- title:
--   Small Pair Seeds 36 checked
-- statement:
--   Auxiliary result `smallPairSeeds_36_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic36.lean, lines 8-11, SHA-256 87b551b70c8e8e7d320aa0b896d859e9400b9dfe6374efbff8a3e882bde27366. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs36_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_36_checked :
    pairSeedsCoveredBool smallPairA_36 smallPairB_36
      seedRootDisk_1_2 smallPairClosure_36 = true := by sorry





end D1Bound5
end
