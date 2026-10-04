-- Prove2me | Theorems.Thm_CookPvsNP_stack_sweep_left
-- name    : CookPvsNP.stack_sweep_left
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T11:35:18.042917+00:00
-- url     : https://prove2.me/theorems/eb3acf1a-c8a5-4d62-92d3-4c8e569cced2
-- title:
--   Exact left sweep of the stack compiler
-- statement:
--   The left-scan state crosses W columns in W transitions, applies the pop carry transform, and arrives at the origin marker with the transformed data on its right.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackCompiler

namespace CookPvsNP
theorem stack_sweep_left {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q) (a : K → StackAct A)
    (c : StackCol K A) (r : List (StackCol K A)) (R : List (Option (StackSym K A))) :
    (stackTM P ki ko).run r.length
      ⟨.scanL q a c,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).tail,
        (r.map (some ∘ StackSym.work) ++ [some (StackSym.origin (K := K) (A := A))]).headD none, R⟩ =
      ⟨.scanL q a (stackLeft a c r).1, [], some (StackSym.origin (K := K) (A := A)),
        ((stackLeft a c r).2.map (some ∘ StackSym.work)).reverse ++ R⟩ := by sorry
end CookPvsNP
