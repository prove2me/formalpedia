-- Prove2me | Theorems.Thm_CookPvsNP_stack_polytime
-- name    : CookPvsNP.stack_polytime
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:05:09.778994+00:00
-- url     : https://prove2.me/theorems/25668b37-fef5-4a94-9c8f-ee4e82aa3cde
-- title:
--   Polynomial finite-stack computations compile to Cook polynomial time
-- statement:
--   A fixed finite-control, finite-alphabet stack machine computing f on a designated output stack within |w|^k+k source steps witnesses CookPvsNP.PolyTimeComputable f. There is no requirement to clear other source stacks; the compiler performs that cleanup.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackRepresentation

namespace CookPvsNP
theorem stack_polytime {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (f : List A → List A) (k : ℕ)
    (h : ∀ w : List A, ∃ m, m ≤ w.length ^ k + k ∧
      P.done ((P.step^[m]) (P.init ki w)).state = true ∧
      ((P.step^[m]) (P.init ki w)).store ko = f w) : PolyTimeComputable f := by sorry
end CookPvsNP
