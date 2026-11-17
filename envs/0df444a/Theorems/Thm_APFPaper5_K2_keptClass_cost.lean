-- Prove2me | Theorems.Thm_APFPaper5_K2_keptClass_cost
-- name    : APFPaper5.K2.keptClass_cost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:31:27.410759+00:00
-- url     : https://prove2.me/theorems/2552a08a-a2a4-4269-9fd3-00e4b6572b77
-- title:
--   keptClass cost
-- statement:
--   Result: keptClass cost. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem keptClass_cost [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool) (S : Finset D) :
--       recordForm w (keptClass keeps S) (keptClass keeps S) = keptCost w keeps S
--   ```
--
--   Module context and limits: Active and signed-side classes are mathematical candidates, not adopted state readings. keptClass represents the recorded part only. Hold transformation rules retain RearrangesFamily and the stated flip assumptions; union additivity requires the explicit union rule and disjoint kept records.
--
--   Source scope parameters:
--
--   ```lean
--   universe uI uX uD uW
--   variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}
--   ```
--
--   Public reference result; this record does not establish Foundation admission, physical K1–K4 closure, a forced transfer or Born-rule derivation.
-- source:
--   ['Theorems.Thm_APFPaper5_K2_state_class_candidates:147; pullbacks v39; source SHA-256 72423d5f7c1afb45e6a16aeca09a021c2de8dc1cacc91a639ea111660cfd570c']

import Definitions.Def_APFPaper5_K2_StateClass
import Definitions.Def_APFPaper5_K2_HoldScore
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum

set_option autoImplicit false
open APFPaper5.K1

namespace APFPaper5.K2
end APFPaper5.K2
open APFPaper5
open APFPaper5.K2
universe uI uX uD uW
variable {ι : Type uI} {X : Type uX} {D : Type uD} {W : Type uW}





/-! ### K1's table is an overlap of record lists -/





/-! ### Candidate A: the distinctions that read true, added up -/









/-! ### Candidate B: the side of each distinction -/





/-! ### Candidate C: the records the held family keeps -/

theorem APFPaper5.K2.keptClass_cost [Fintype W] (w : W → ℝ) (keeps : Finset D → W → Bool) (S : Finset D) :
    recordForm w (keptClass keeps S) (keptClass keeps S) = keptCost w keeps S := by sorry
