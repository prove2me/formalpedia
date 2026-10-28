-- Prove2me | Theorems.Thm_D1Bound5_smallPairSeeds_35_checked
-- name    : D1Bound5.smallPairSeeds_35_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T01:25:18.982216+00:00
-- url     : https://prove2.me/theorems/b97d4afd-21c3-4c6c-b873-f36c3a96e1a1
-- title:
--   Small Pair Seeds 35 checked
-- statement:
--   Auxiliary result `smallPairSeeds_35_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallPairGraphArithmetic35.lean, lines 8-11, SHA-256 d01b9fe55b1372883ffb9a877d397cc0e229add28418a1d693cfb93658e97df3. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_001
import Definitions.Def_D1Bound5_SmallPairGraphInputs35_Definitions_002

section
namespace D1Bound5
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem _root_.D1Bound5.smallPairSeeds_35_checked :
    pairSeedsCoveredBool smallPairA_35 smallPairB_35
      seedRootDisk_1_2 smallPairClosure_35 = true := by sorry





end D1Bound5
end
