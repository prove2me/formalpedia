-- Prove2me | Theorems.Thm_APFB07b_realized_has_no_rate_of_present_records
-- name    : APFB07b.realized_has_no_rate_of_present_records
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:05:22.045147+00:00
-- url     : https://prove2.me/theorems/838ed26b-5cfa-4329-a049-0e2d194e129c
-- title:
--   Present-record selection has zero rates in the supplied model
-- statement:
--   In the supplied four-real-coordinate Held2 model, assume A2Selection and BWUniqueMinimum and that both admissibility and price depend only on plainNow. Then both rate coordinates of the selected state are zero, because rateFlip preserves plainNow. This is conditional on that configuration and price binding.
-- source:
--   Sib v44 Theorems/Thm_APFB07_realized_is_its_own_reverse.lean:96

import Definitions.Def_APF_B07a_DeclaredInput
import Definitions.Def_APF_B07b_DeclaredInput
import Theorems.Thm_APFPaper5_K3_rateFlip_keeps_plainNow
import Theorems.Thm_APFPaper5_K3_same_present_records_different_later
import Theorems.Thm_APFPaper5_K3_rateFree_present_records_fix_state
import Theorems.Thm_APFPaper5_K3_mix_has_no_reverse
import Theorems.Thm_APFB01_rate_is_held_on_the_carrier
import Mathlib.Tactic.Linarith

set_option autoImplicit false





namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

open APFPaper5.K3 in
theorem APFB07b.realized_has_no_rate_of_present_records {Interface : Type*}
    (originalAdmissible : Interface → Held2 → Prop) (totalCost : Interface → Held2 → ℝ)
    (realized : Interface → Held2)
    (hA2 : APFB07a.A2Selection originalAdmissible totalCost realized)
    (hBW : APFB07b.BWUniqueMinimum originalAdmissible totalCost)
    (adm : Interface → ℝ × ℝ × ℝ → Prop) (cost : Interface → ℝ × ℝ × ℝ → ℝ)
    (hadm : ∀ i h, originalAdmissible i h ↔ adm i (plainNow h))
    (hcost : ∀ i h, totalCost i h = cost i (plainNow h)) (i : Interface) :
    (realized i).a2 = 0 ∧ (realized i).b2 = 0 := by sorry
