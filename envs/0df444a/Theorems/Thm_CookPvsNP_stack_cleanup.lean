-- Prove2me | Theorems.Thm_CookPvsNP_stack_cleanup
-- name    : CookPvsNP.stack_cleanup
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:04:50.164274+00:00
-- url     : https://prove2.me/theorems/9d81df35-9100-4d6e-8f7d-0e76460ec6be
-- title:
--   Exact output cleanup for the finite-stack Cook compiler
-- statement:
--   A source-halting frame of positive width W reaches the Cook accepting state in 2W+2 transitions. Its head and right list contain the output projection plus a trailing blank.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackRepresentation

namespace CookPvsNP
theorem stack_cleanup {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q)
    (x : StackCol K A) (xs : List (StackCol K A)) (hq : P.done q = true) :
    let out := (x :: xs).map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    (stackTM P ki ko).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      ⟨.accept, [some (StackSym.origin (K := K) (A := A))], out.headD none, out.tail⟩ := by sorry
end CookPvsNP
