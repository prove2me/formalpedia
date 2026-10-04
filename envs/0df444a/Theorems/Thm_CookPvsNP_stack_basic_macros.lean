-- Prove2me | Theorems.Thm_CookPvsNP_stack_basic_macros
-- name    : CookPvsNP.stack_basic_macros
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:36:26.271916+00:00
-- url     : https://prove2.me/theorems/1a6b7173-fbcb-4a65-ab2c-d21eb6993054
-- title:
--   stack basic macros
-- statement:
--   Push and pop take one step, and clearing a stack takes three times its length plus one steps.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackMacros
open CookPvsNP

namespace CookPvsNP
theorem stack_basic_macros {K A : Type} [DecidableEq K] (k : K) (s : K → List A) :
    (∀ a : A, (pushProg k a).Exec s (Function.update s k (a :: s k)) 1) ∧
    (popProg k).Exec s (Function.update s k (s k).tail) 1 ∧
    (clearProg k).Exec s (Function.update s k []) (3 * (s k).length + 1) := by sorry
end CookPvsNP
