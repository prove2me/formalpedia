-- Prove2me | Theorems.Thm_CookPvsNP_stack_transfer
-- name    : CookPvsNP.stack_transfer
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:36:33.807202+00:00
-- url     : https://prove2.me/theorems/e40f5740-9c1d-4dfc-844a-258e1f6ed29c
-- title:
--   stack transfer
-- statement:
--   Transfer reverses the source into selected targets and empties the source in exactly three times its length plus one steps.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros
open CookPvsNP

namespace CookPvsNP
theorem stack_transfer {K A : Type} [DecidableEq K] (src : K) (targets : K → Bool)
    (s : K → List A) :
    (transferProg src targets).Exec s (transferStore src targets s) (3 * (s src).length + 1) := by sorry
end CookPvsNP
