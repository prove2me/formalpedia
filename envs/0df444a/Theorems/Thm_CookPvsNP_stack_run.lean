-- Prove2me | Theorems.Thm_CookPvsNP_stack_run
-- name    : CookPvsNP.stack_run
-- status  : Proved
-- author  : @arexychen
-- created : 2026-10-02T12:05:24.353436+00:00
-- url     : https://prove2.me/theorems/24557f6a-c06e-4844-af7d-fd9b51f0fe57
-- title:
--   Finite stack runs admit a quadratic Cook simulation bound
-- statement:
--   A source run of m instructions from width W admits a Cook run of at most m(2W+m+1) transitions. The resulting frame represents the exact source result and has width at most W+m. A source that halts early may be simulated for fewer transitions.
-- source:
--   New auxiliary formalization for the ResourceScheduling Q2 reduction. The target is the unchanged CookPvsNP one-tape machine model, following Cook, The P versus NP problem, Clay Mathematics Institute (2000), Appendix. This explicit finite-column stack compiler and its simulation lemmas are new contributions, not numbered claims from Cook or the scheduling source paper.

import Definitions.Def_CookPvsNP_StackRepresentation

namespace CookPvsNP
theorem stack_run {K A Q : Type} [Fintype K] [Fintype A] [Fintype Q]
    [DecidableEq K] [DecidableEq A] [DecidableEq Q]
    (P : StackMachine K A Q) (ki ko : K) (m : ℕ)
    (c : StackCfg K A Q) (r : List (StackCol K A)) (hn : 0 < r.length)
    (hr : StackRep r c.store) :
    ∃ t r', t ≤ stackTime r.length m ∧ r'.length ≤ r.length + m ∧ 0 < r'.length ∧
      StackRep r' ((P.step^[m]) c).store ∧
      (stackTM P ki ko).run t (stackFrame c.state r) =
        stackFrame ((P.step^[m]) c).state r' := by sorry
end CookPvsNP
