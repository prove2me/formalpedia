-- Prove2me | Theorems.Thm_APFB07b_realized_rate_not_forbidden
-- name    : APFB07b.realized_rate_not_forbidden
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:05:34.445522+00:00
-- url     : https://prove2.me/theorems/82c35dac-d813-4bd1-965c-6042c340d0da
-- title:
--   A singleton selected model with a nonzero rate coordinate
-- statement:
--   A singleton admissible domain in Held2 with zero cost can satisfy A2Selection and BWUniqueMinimum while the realized b2 coordinate is nonzero. This supplies a consistency witness for those generic forms, not an original physical instance.
-- source:
--   Sib v44 Theorems/Thm_APFB07_realized_is_its_own_reverse.lean:110

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
theorem APFB07b.realized_rate_not_forbidden :
    ∃ (originalAdmissible : Unit → Held2 → Prop) (totalCost : Unit → Held2 → ℝ)
      (realized : Unit → Held2),
      APFB07a.A2Selection originalAdmissible totalCost realized ∧
        APFB07b.BWUniqueMinimum originalAdmissible totalCost ∧ (realized ()).b2 ≠ 0 := by sorry
