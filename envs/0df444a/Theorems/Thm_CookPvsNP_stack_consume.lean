-- Prove2me | Theorems.Thm_CookPvsNP_stack_consume
-- name    : CookPvsNP.stack_consume
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:36:45.533498+00:00
-- url     : https://prove2.me/theorems/24103bf3-d14d-4543-80a7-c21e11a9d86e
-- title:
--   stack consume
-- statement:
--   Consuming a counter drops its length from selected stacks and takes three times the counter length plus one steps.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros
open CookPvsNP

namespace CookPvsNP
theorem stack_consume {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) :
    (consumeProg src targets).Exec s (consumeStore src targets s) (3 * (s src).length + 1) := by sorry
end CookPvsNP
