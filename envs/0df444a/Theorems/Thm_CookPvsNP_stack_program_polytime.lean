-- Prove2me | Theorems.Thm_CookPvsNP_stack_program_polytime
-- name    : CookPvsNP.stack_program_polytime
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:36:53.84822+00:00
-- url     : https://prove2.me/theorems/1071e0cd-eeb2-4a26-a590-816612bb85fa
-- title:
--   stack program polytime
-- statement:
--   Polynomially bounded executions of a fixed structured stack program imply Cook polynomial-time computability of its designated output.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackProgram
open CookPvsNP

namespace CookPvsNP
theorem stack_program_polytime {K A : Type} [Fintype K] [Fintype A] [DecidableEq K] [DecidableEq A]
    (p : StackProg K A) (ki ko : K) (f : List A → List A) (k : ℕ)
    (h : ∀ w : List A, ∃ s n, n ≤ w.length ^ k + k ∧
      p.Exec (fun j => if j = ki then w else []) s n ∧ s ko = f w) :
    PolyTimeComputable f := by sorry
end CookPvsNP
