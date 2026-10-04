-- Prove2me | Theorems.Thm_CookPvsNP_stack_specification_loop
-- name    : CookPvsNP.stack_specification_loop
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:36:53.028241+00:00
-- url     : https://prove2.me/theorems/0a7a87d4-8808-45b7-b845-a70212ba2528
-- title:
--   stack specification loop
-- statement:
--   A represented loop whose natural rank drops by one implements the corresponding iterate with the sum of certified body costs and loop overhead.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackSpecification
open CookPvsNP

namespace CookPvsNP
theorem stack_specification_loop {K A S : Type} (R : S → (K → List A) → Prop)
    (p : StackProg K A) (test : (K → Option A) → Bool) (f : S → S) (cost rank : S → ℕ)
    (hp : StackImplements R p f cost)
    (ht : ∀ s l, R s l → test (fun k => (l k).head?) = decide (0 < rank s))
    (hd : ∀ s, 0 < rank s → rank (f s) + 1 = rank s) :
    StackImplements R (StackProg.loop test p) (fun s => (f^[rank s]) s)
      (fun s => stackLoopCost f cost (rank s) s) := by sorry
end CookPvsNP
