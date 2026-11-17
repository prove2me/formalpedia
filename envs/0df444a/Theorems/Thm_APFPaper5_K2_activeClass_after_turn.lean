-- Prove2me | Theorems.Thm_APFPaper5_K2_activeClass_after_turn
-- name    : APFPaper5.K2.activeClass_after_turn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-16T15:29:11.802199+00:00
-- url     : https://prove2.me/theorems/92361738-530d-41c2-9542-9f22d5f19c78
-- title:
--   activeClass after turn
-- statement:
--   Result: activeClass after turn. All parameters and hypotheses are retained in the declaration below.
--
--   ```lean
--   theorem activeClass_after_turn (reads : D → X → Bool) (dist : ι → D) (h : X → X)
--       (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
--       (i : ι) (hi : flip i = true) (x : X) :
--       activeClass reads dist (h x) i = 1 - heldAfter sigma (activeClass reads dist x) i
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
--   ['Theorems.Thm_APFPaper5_K2_state_class_candidates:101; pullbacks v39; source SHA-256 72423d5f7c1afb45e6a16aeca09a021c2de8dc1cacc91a639ea111660cfd570c']

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

theorem APFPaper5.K2.activeClass_after_turn (reads : D → X → Bool) (dist : ι → D) (h : X → X)
    (sigma : ι → ι) (flip : ι → Bool) (r : RearrangesFamily reads dist h sigma flip)
    (i : ι) (hi : flip i = true) (x : X) :
    activeClass reads dist (h x) i = 1 - heldAfter sigma (activeClass reads dist x) i := by sorry
