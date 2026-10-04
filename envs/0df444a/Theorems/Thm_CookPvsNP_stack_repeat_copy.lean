-- Prove2me | Theorems.Thm_CookPvsNP_stack_repeat_copy
-- name    : CookPvsNP.stack_repeat_copy
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T14:00:00.256004+00:00
-- url     : https://prove2.me/theorems/3e8c6338-2334-4e60-b9cd-59cc20462f16
-- title:
--   stack repeat copy
-- statement:
--   Repeated copying prepends the replicated source word, consumes the counter, and has the stated bilinear source-step count.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackRepeat
open CookPvsNP

namespace CookPvsNP
theorem stack_repeat_copy {K A : Type} [DecidableEq K] (r : Fin 4 ↪ K)
    (s : K → List A) (he : s (r 3) = []) :
    (repeatCopyProg r).Exec s
      (Function.update (Function.update s (r 2) []) (r 1)
        ((List.replicate (s (r 2)).length (s (r 0))).flatten ++ s (r 1)))
      ((6 * (s (r 0)).length + 7) * (s (r 2)).length + 1) := by sorry
end CookPvsNP
