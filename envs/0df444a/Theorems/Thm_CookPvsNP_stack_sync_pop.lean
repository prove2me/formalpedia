-- Prove2me | Theorems.Thm_CookPvsNP_stack_sync_pop
-- name    : CookPvsNP.stack_sync_pop
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:00:21.582283+00:00
-- url     : https://prove2.me/theorems/ed051e61-8303-4a3a-9446-85e60aa5a9cd
-- title:
--   stack sync pop
-- statement:
--   Synchronous popping drops the minimum of both stack lengths from each stack in three times that minimum plus one steps.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackCompare
open CookPvsNP

namespace CookPvsNP
theorem stack_sync_pop {K A : Type} [DecidableEq K] (i j : K) (hne : i ≠ j) (s : K → List A) :
    let m := min (s i).length (s j).length
    (syncPopProg i j).Exec s (Function.update (Function.update s i ((s i).drop m)) j ((s j).drop m))
      (3 * m + 1) := by sorry
end CookPvsNP
