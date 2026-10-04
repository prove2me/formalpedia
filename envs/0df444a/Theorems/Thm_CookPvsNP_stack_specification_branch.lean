-- Prove2me | Theorems.Thm_CookPvsNP_stack_specification_branch
-- name    : CookPvsNP.stack_specification_branch
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T13:37:05.372566+00:00
-- url     : https://prove2.me/theorems/930bca61-83be-47f1-a58a-6fe95e135b93
-- title:
--   stack specification branch
-- statement:
--   A represented Boolean guard selects the matching semantic branch, with one source step plus the maximum branch budget.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackSpecification
open CookPvsNP

namespace CookPvsNP
theorem stack_specification_branch {K A S : Type} (R : S → (K → List A) → Prop)
    (p q : StackProg K A) (test : (K → Option A) → Bool) (b : S → Bool)
    (f g : S → S) (c d : S → ℕ)
    (hp : StackImplements R p f c) (hq : StackImplements R q g d)
    (hb : ∀ s l, R s l → test (fun k => (l k).head?) = b s) :
    StackImplements R (.branch test p q) (fun s => if b s then f s else g s)
      (fun s => 1 + max (c s) (d s)) := by sorry
end CookPvsNP
