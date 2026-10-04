-- Prove2me | Theorems.Thm_CookPvsNP_stack_setup
-- name    : CookPvsNP.stack_setup
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T11:35:11.008258+00:00
-- url     : https://prove2.me/theorems/73c0a25a-4b15-4b56-860c-ead7287bcfa6
-- title:
--   Exact input setup for the finite-stack Cook compiler
-- statement:
--   On input w, the compiler reaches its initial source frame in 2|w|+4 transitions. Its columns contain w in the input stack and end with one all-blank column.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackCompiler

namespace CookPvsNP
theorem stack_setup {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (w : List A) :
    (stackTM P ki ko).run (2 * w.length + 4)
      ((stackTM P ki ko).init (w.map stackInput)) =
      stackFrame P.initial (w.map (stackInitialCol ki) ++ [stackZero]) := by sorry
end CookPvsNP
