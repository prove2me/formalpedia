-- Prove2me | Theorems.Thm_D1Bound5_smallTripleSeeds_10_checked
-- name    : D1Bound5.smallTripleSeeds_10_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:43:49.24476+00:00
-- url     : https://prove2.me/theorems/f83835db-8b02-47a2-bd41-25d90512eeb0
-- title:
--   Small Triple Seeds 10 checked
-- statement:
--   Auxiliary result `smallTripleSeeds_10_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData10.lean, lines 74-77, SHA-256 f02e6c8d015b4e0538aba168e1bf2bb6744d45b1838d92210a569eb6c517214d. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData10_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000









theorem _root_.D1Bound5.smallTripleSeeds_10_checked :
    pairSeedsCoveredBool smallTripleAnchorA_10 smallTripleAnchorB_10
      seedRootDisk_1_2 smallTriplePairClosure_10 = true := by sorry







end D1Bound5
end
