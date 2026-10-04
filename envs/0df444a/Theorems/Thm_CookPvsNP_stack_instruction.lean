-- Prove2me | Theorems.Thm_CookPvsNP_stack_instruction
-- name    : CookPvsNP.stack_instruction
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:04:40.912017+00:00
-- url     : https://prove2.me/theorems/9897566b-d419-40a9-9f88-7e2686cc9cd4
-- title:
--   A stack instruction takes exactly two sweeps plus two transitions
-- statement:
--   On a nonempty width-W frame whose source control is not halting, the Cook compiler reaches the next source control and transformed columns in exactly 2W+2 transitions.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackRepresentation

namespace CookPvsNP
theorem stack_instruction {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (q : Q)
    (x : StackCol K A) (xs : List (StackCol K A)) (hq : P.done q = false) :
    let d := P.next q x
    (stackTM P ki ko).run (2 * (x :: xs).length + 2) (stackFrame q (x :: xs)) =
      stackFrame d.1 (stackBackward d.2 (stackForward d.2 (stackPushCarry d.2) (x :: xs))) := by sorry
end CookPvsNP
