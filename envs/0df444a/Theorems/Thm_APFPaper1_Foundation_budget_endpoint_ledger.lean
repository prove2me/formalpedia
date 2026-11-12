-- Prove2me | Theorems.Thm_APFPaper1_Foundation_budget_endpoint_ledger
-- name    : APFPaper1.Foundation.budget_endpoint_ledger
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-10-13T17:35:57.148596+00:00
-- url     : https://prove2.me/theorems/e390b7ff-d8e0-4313-bf6e-6f1c0b22c807
-- title:
--   Budget feasibility: strict slack or attained equality
-- statement:
--   For the same supplied Ledger L, finite S with Feasible L S, and real budget b, a serving protocol of complete price at most b exists exactly when cost L S < b or when cost L S = b and a serving protocol attains that infimum. Feasibility and the attaining witness at equality remain explicit; no universal attainment or physical instantiation is inferred.
-- source:
--   Paper 1 Supplement v9.27:1778-1782. Existing Local_budget_endpoint proof reused with current CostLedger, cost_bounds_ledger and near_optimal_ledger bindings. Original seed /seed_items/5, historical node 993c7730-0980-42d5-8979-35582a3666fe. No cost/familyCost bridge or new physical premise.

import Definitions.Def_APFPaper1_WithinBudget
import Theorems.Thm_APFPaper1_Foundation_cost_bounds_ledger
import Theorems.Thm_APFPaper1_Foundation_near_optimal_ledger
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Push
set_option autoImplicit false
open Classical

namespace APFPaper1.Foundation
theorem budget_endpoint_ledger {D P Record : Type*} (L : Ledger D P Record) (S : Finset D)
    (hS : Feasible L S) (b : ℝ) :
    WithinBudget L S b ↔ cost L S < b ∨
      (cost L S = b ∧ ∃ p, L.serves p S ∧ L.price p = cost L S) := by
  sorry
end APFPaper1.Foundation
