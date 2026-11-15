-- Prove2me | Theorems.Thm_APFPaper5_K3_present_records_do_not_fix_next
-- name    : APFPaper5.K3.present_records_do_not_fix_next
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:11:23.61249+00:00
-- url     : https://prove2.me/theorems/442618cb-2c4c-422f-bc66-09f30233c2ab
-- title:
--   Present records do not fix next
-- statement:
--   No function of the plainNow triple alone reproduces plainNow after the relative quarter turn for every Held2 state. Keep s nonzero, unit-pair conditions where present, and nonzero a*b for distinct orbit states. There is no assertion that these turns are admitted physical holds.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_relation_and_reverse.lean', 'sha256': 'b96d3a0e70f21b697ca8236fd50702872ad89fc693bbf0bef8035686c119aa68', 'line': 150, 'declaration': 'APFPaper5.K3.present_records_do_not_fix_next'}]

import Theorems.Thm_APFPaper5_K3_rateFlip_keeps_plainNow
import Theorems.Thm_APFPaper5_K3_same_present_records_different_later
import Theorems.Thm_APFPaper5_K3_rateFree_present_records_fix_state
import Theorems.Thm_APFPaper5_K3_mix_has_no_reverse
import Theorems.Thm_APFB01_rate_is_held_on_the_carrier
import Theorems.Thm_APFPaper5_K3_profile_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFB01_quarter_record_descends
import Theorems.Thm_APFPaper5_K3_closing_orbit_does_not_move
import Theorems.Thm_APFPaper5_K3_number_alone_does_not_fix_next
import Theorems.Thm_APFPaper5_K3_retracing_orbit_same_now_different_later
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.present_records_do_not_fix_next :
    ¬ ∃ f : ℝ × ℝ × ℝ → ℝ × ℝ × ℝ, ∀ h : Held2, plainNow (relativeTurn 0 1 h) = f (plainNow h) := by sorry
