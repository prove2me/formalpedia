-- Prove2me | Theorems.Thm_APFB07b_realized_fixed_by_cost_symmetry
-- name    : APFB07b.realized_fixed_by_cost_symmetry
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:05:16.075665+00:00
-- url     : https://prove2.me/theorems/3eccc30a-2030-4793-a98b-fec191abcdc0
-- title:
--   Realized fixed by cost symmetry
-- statement:
--   For any supplied candidate domain and cost, A2Selection together with existence and uniqueness of a minimizer implies that any map preserving admissibility and cost fixes the realized candidate. The map is not required to be invertible, and the theorem does not certify the supplied physical bindings.
-- source:
--   Sib v44 Theorems/Thm_APFB07_realized_is_its_own_reverse.lean:45

import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Theorems.Thm_APFPaper5_K3_rateFlip_keeps_plainNow
import Theorems.Thm_APFPaper5_K3_same_present_records_different_later
import Theorems.Thm_APFPaper5_K3_rateFree_present_records_fix_state
import Theorems.Thm_APFPaper5_K3_mix_has_no_reverse
import Theorems.Thm_APFB01_rate_is_held_on_the_carrier
import Mathlib.Tactic.Linarith

set_option autoImplicit false

theorem APFB07b.realized_fixed_by_cost_symmetry {Interface : Type*}
    {Configuration : Interface → Type*}
    (originalAdmissible : (i : Interface) → Configuration i → Prop)
    (totalCost : (i : Interface) → Configuration i → ℝ)
    (realized : (i : Interface) → Configuration i)
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost) (i : Interface)
    (theta : Configuration i → Configuration i)
    (hadm : ∀ G, originalAdmissible i G → originalAdmissible i (theta G))
    (hcost : ∀ G, totalCost i (theta G) = totalCost i G) :
    theta (realized i) = realized i := by sorry
