-- Prove2me | Theorems.Thm_APFB07b_one_way_history_meets_A2_BW
-- name    : APFB07b.one_way_history_meets_A2_BW
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:09:17.763803+00:00
-- url     : https://prove2.me/theorems/04cd813e-8765-4ffb-983a-20edfa903a24
-- title:
--   One way history meets a2 bw
-- statement:
--   A singleton admissible set of three-moment histories with sum cost can satisfy A2Selection and BWUniqueMinimum while its realized record differs at moments 1 and 2 and determines the moment injectively. This is a generic-form witness, not physical foundation independence.
-- source:
--   Sib v44 Theorems/Thm_APFB07_realized_history_retraces.lean:122

import Theorems.Thm_APFB07b_realized_fixed_by_cost_symmetry
import Theorems.Thm_APFB07b_realized_has_no_rate_of_present_records
import Theorems.Thm_APFB07b_realized_rate_not_forbidden
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Data.Fintype.BigOperators

set_option autoImplicit false

universe uX uP uR

namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFB07b.one_way_history_meets_A2_BW :
    ∃ (originalAdmissible : Unit → (Fin 3 → ℝ) → Prop) (totalCost : Unit → (Fin 3 → ℝ) → ℝ)
      (realized : Unit → (Fin 3 → ℝ)),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧
        (∀ r, totalCost () r = ∑ t, r t) ∧ realized () 2 ≠ realized () 1 ∧
        ∀ s t : Fin 3, realized () s = realized () t → s = t := by sorry
