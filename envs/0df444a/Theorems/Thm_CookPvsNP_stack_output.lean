-- Prove2me | Theorems.Thm_CookPvsNP_stack_output
-- name    : CookPvsNP.stack_output
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:05:08.507579+00:00
-- url     : https://prove2.me/theorems/89bd352c-6200-4e92-8aab-aacd5a374da3
-- title:
--   The cleaned stack frame has the exact ordinary word output
-- statement:
--   For a valid padded stack representation, the cleanup configuration's Cook output is exactly the designated stack under the ordinary output embedding.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackRepresentation

namespace CookPvsNP
theorem stack_output {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (r : List (StackCol K A))
    (s : K → List A) (hr : StackRep r s) :
    let out := r.map (fun v => (v ko).map (StackSym.output (K := K))) ++ [none]
    (stackTM P ki ko).output
      ⟨.accept, [some .origin], out.headD none, out.tail⟩ =
      (s ko).map (some ∘ stackOutput) := by sorry
end CookPvsNP
