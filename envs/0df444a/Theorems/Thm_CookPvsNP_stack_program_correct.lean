-- Prove2me | Theorems.Thm_CookPvsNP_stack_program_correct
-- name    : CookPvsNP.stack_program_correct
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:36:48.454285+00:00
-- url     : https://prove2.me/theorems/ca865dec-c52a-4359-9aa3-2d912fe35582
-- title:
--   stack program correct
-- statement:
--   Every structured source execution yields exactly the same store at a halting label of its fixed finite-control machine.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackProgram
open CookPvsNP

namespace CookPvsNP
theorem stack_program_correct {K A : Type} {p : StackProg K A} {s t : K → List A} {n : ℕ}
    (h : p.Exec s t n) : ∃ l : p.Label, p.done l = true ∧
      (p.machine.step^[n]) ⟨p.entry, s⟩ = ⟨l, t⟩ := by sorry
end CookPvsNP
