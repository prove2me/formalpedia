-- Prove2me | Theorems.Thm_CookPvsNP_stack_specification_seq
-- name    : CookPvsNP.stack_specification_seq
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:37:00.921317+00:00
-- url     : https://prove2.me/theorems/7fa1a8f9-0f95-4c9d-a15a-5f9cdcd62a46
-- title:
--   stack specification seq
-- statement:
--   Semantic stack implementations compose with one source step of sequencing overhead.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackSpecification
open CookPvsNP

namespace CookPvsNP
theorem stack_specification_seq {K A S : Type} (R : S → (K → List A) → Prop)
    (p q : StackProg K A) (f g : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hq : StackImplements R q g d) :
    StackImplements R (p.seq q) (g ∘ f) (fun s => c s + 1 + d (f s)) := by sorry
end CookPvsNP
