-- Prove2me | Theorems.Thm_CookPvsNP_stack_copy
-- name    : CookPvsNP.stack_copy
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:36:18.820601+00:00
-- url     : https://prove2.me/theorems/bc7bb049-1cb2-4e63-ad70-bd31ebafd3a9
-- title:
--   stack copy
-- statement:
--   Copy preserves the source, prepends it to the destination, restores empty scratch, and takes six times source length plus three steps.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros
open CookPvsNP

namespace CookPvsNP
theorem stack_copy {K A : Type} [DecidableEq K] (src dst scratch : K)
    (hsd : src ≠ dst) (hst : src ≠ scratch) (hdt : dst ≠ scratch)
    (s : K → List A) (he : s scratch = []) :
    (copyProg src dst scratch).Exec s
      (Function.update s dst (s src ++ s dst)) (6 * (s src).length + 3) := by sorry
end CookPvsNP
