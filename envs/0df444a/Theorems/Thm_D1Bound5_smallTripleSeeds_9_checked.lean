-- Prove2me | Theorems.Thm_D1Bound5_smallTripleSeeds_9_checked
-- name    : D1Bound5.smallTripleSeeds_9_checked
-- status  : Proved
-- author  : @tp
-- created : 2026-10-24T00:48:01.473959+00:00
-- url     : https://prove2.me/theorems/27e43764-b5a8-45e8-94fb-6c7093c5b1ea
-- title:
--   Small Triple Seeds 9 checked
-- statement:
--   Auxiliary result `smallTripleSeeds_9_checked` in the proof of the bound five for Diophantine D(1) sets in imaginary quadratic integer rings. The formal statement specifies its hypotheses and conclusion; a mathematical prose description remains to be supplied.
-- source:
--   D1Bound5/SmallTripleExtensionData9.lean, lines 102-105, SHA-256 d547b2c59760d0754a4660f0e6f6a2dd995b480c12bf4f53eac6fc574c6b3772. Project: https://github.com/tomislav-math/d1-bound5-lean

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
import Definitions.Def_D1Bound5_SmallTripleExtensionData9_Definitions

section
namespace D1Bound5
open QuadInt
set_option maxRecDepth 32768
set_option maxHeartbeats 8000000









theorem _root_.D1Bound5.smallTripleSeeds_9_checked :
    pairSeedsCoveredBool smallTripleAnchorA_9 smallTripleAnchorB_9
      seedRootDisk_1_2 smallTriplePairClosure_9 = true := by sorry







end D1Bound5
end
