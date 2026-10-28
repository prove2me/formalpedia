-- Prove2me | Theorems.Thm_D1Bound5_smallTripleSeeds_1_checked
-- name    : D1Bound5.smallTripleSeeds_1_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:41:42.566097+00:00
-- url     : https://prove2.me/theorems/da84f382-fa98-4f48-9ad1-3f7ca82cc97e
-- title:
--   Small Triple Seeds 1 checked
-- statement:
--   Auxiliary result `smallTripleSeeds_1_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData1.lean, lines 80-83, SHA-256 03e5796cc7e31c4d4194e8e368dfed993f810968002b0f261d7097b40a9f996b. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData1_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000









theorem _root_.D1Bound5.smallTripleSeeds_1_checked :
    pairSeedsCoveredBool smallTripleAnchorA_1 smallTripleAnchorB_1
      seedRootDisk_0_1 smallTriplePairClosure_1 = true := by sorry







end D1Bound5
end
