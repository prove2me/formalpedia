-- Prove2me | Theorems.Thm_CookPvsNP_stack_sweep_right
-- name    : CookPvsNP.stack_sweep_right
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T11:35:02.407956+00:00
-- url     : https://prove2.me/theorems/83e47ebd-9d37-4a4a-8b9f-a7749a07fd69
-- title:
--   Exact right sweep of the stack compiler
-- statement:
--   The right-scan state processes a list of W columns in exactly W Cook transitions, writes the forward carry transformation, and arrives at the blank after the columns.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackCompiler

namespace CookPvsNP
theorem stack_sweep_right {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q) (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (L : List (Option (StackSym K A))) :
    (stackTM P ki ko).run r.length
      ⟨.scanR q a c, L, (r.map (some ∘ StackSym.work)).headD none,
        (r.map (some ∘ StackSym.work)).tail⟩ =
      ⟨.scanR q a (stackRight a c r).1,
        ((stackRight a c r).2.map (some ∘ StackSym.work)).reverse ++ L, none, []⟩ := by sorry
end CookPvsNP
