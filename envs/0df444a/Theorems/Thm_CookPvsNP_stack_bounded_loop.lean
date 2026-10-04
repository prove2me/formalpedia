-- Prove2me | Theorems.Thm_CookPvsNP_stack_bounded_loop
-- name    : CookPvsNP.stack_bounded_loop
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:37:02.832991+00:00
-- url     : https://prove2.me/theorems/8ce46be7-a4fc-451d-91d5-fd60c4927405
-- title:
--   stack bounded loop
-- statement:
--   A loop with n certified body executions, correct guards, and body cost at most B executes in at most n(B+2)+1 source steps.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackProgram
open CookPvsNP

namespace CookPvsNP
theorem stack_bounded_loop {K A : Type} (test : (K → Option A) → Bool) (p : StackProg K A)
    (n : ℕ) (s : ℕ → K → List A) (cost : ℕ → ℕ) (B : ℕ)
    (hg : ∀ i < n, test (fun k => (s i k).head?) = true)
    (he : test (fun k => (s n k).head?) = false)
    (hb : ∀ i < n, p.Exec (s i) (s (i + 1)) (cost i))
    (hc : ∀ i < n, cost i ≤ B) :
    ∃ t ≤ n * (B + 2) + 1, (StackProg.loop test p).Exec (s 0) (s n) t := by sorry
end CookPvsNP
