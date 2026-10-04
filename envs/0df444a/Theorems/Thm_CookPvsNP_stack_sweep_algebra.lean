-- Prove2me | Theorems.Thm_CookPvsNP_stack_sweep_algebra
-- name    : CookPvsNP.stack_sweep_algebra
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T11:01:45.144978+00:00
-- url     : https://prove2.me/theorems/aa2c5649-3341-45aa-8232-fc178385bc30
-- title:
--   Two sweep accumulators agree with the column transformation
-- statement:
--   The right accumulator preserves the length of its written prefix; a subsequent left accumulator followed by the final carry column equals the specified column transformation.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackModel

namespace CookPvsNP
theorem stack_sweep_algebra {K A : Type} (a : K → StackAct A) (r : List (StackCol K A)) :
    let z := stackRight a (stackPushCarry a) r
    z.2.length = r.length ∧
    (stackLeft a z.1 z.2.reverse).2.reverse ++ [z.1] =
      stackBackward a (stackForward a (stackPushCarry a) r) := by sorry
end CookPvsNP
