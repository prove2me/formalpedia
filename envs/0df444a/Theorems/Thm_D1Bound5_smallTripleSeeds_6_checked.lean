-- Prove2me | Theorems.Thm_D1Bound5_smallTripleSeeds_6_checked
-- name    : D1Bound5.smallTripleSeeds_6_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:42:01.654364+00:00
-- url     : https://prove2.me/theorems/14ef6984-174e-40e6-8fcf-4cbe986ed079
-- title:
--   Small Triple Seeds 6 checked
-- statement:
--   Auxiliary result `smallTripleSeeds_6_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData6.lean, lines 131-134, SHA-256 36f224d3730e31a0a51a42e087cb11043ed4d384f831a7959f50bfd1ed91e3aa. Project: https://github.com/tomislav-math/d1-bound5-lean

import Mathlib.Algebra.QuadraticAlgebra.Basic
import Mathlib.Algebra.Ring.Basic
import Mathlib.Algebra.Ring.Equiv
import Mathlib.Data.Finset.Card
import Mathlib.Data.Finset.Prod
import Mathlib.Data.Int.Interval
import Mathlib.Data.Int.Sqrt
import Mathlib.Data.List.Range
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.LinearCombination
import Definitions.Def_D1Bound5_Coordinates_Definitions
import Definitions.Def_D1Bound5_PairExtensionCore_Definitions
import Definitions.Def_D1Bound5_PairSeedDisks_Definitions
import Definitions.Def_D1Bound5_SmallTripleExtensionData6_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000









theorem _root_.D1Bound5.smallTripleSeeds_6_checked :
    pairSeedsCoveredBool smallTripleAnchorA_6 smallTripleAnchorB_6
      seedRootDisk_1_1 smallTriplePairClosure_6 = true := by sorry







end D1Bound5
end
