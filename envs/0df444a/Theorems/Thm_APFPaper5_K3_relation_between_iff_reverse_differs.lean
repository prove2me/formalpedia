-- Prove2me | Theorems.Thm_APFPaper5_K3_relation_between_iff_reverse_differs
-- name    : APFPaper5.K3.relation_between_iff_reverse_differs
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:11:16.105967+00:00
-- url     : https://prove2.me/theorems/f952bb4f-6f8f-49ad-bfe7-4ae7660e030a
-- title:
--   Relation between if and only if reverse differs
-- statement:
--   For s nonzero, the strict crossRe-squared versus recA*recB inequality is equivalent to different present records after relativeTurn c s for a state and its rate flip. Keep s nonzero, unit-pair conditions where present, and nonzero a*b for distinct orbit states. There is no assertion that these turns are admitted physical holds.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1650'}, {'path': 'source/Theorems/Thm_APFPaper5_K3_relation_and_reverse.lean', 'sha256': 'b96d3a0e70f21b697ca8236fd50702872ad89fc693bbf0bef8035686c119aa68', 'line': 92, 'declaration': 'APFPaper5.K3.relation_between_iff_reverse_differs'}]

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

theorem APFPaper5.K3.relation_between_iff_reverse_differs (c s : ℝ) (hs : s ≠ 0) (h : Held2) :
    crossRe h * crossRe h < recA h * recB h ↔
      plainNow (relativeTurn c s (rateFlip h)) ≠ plainNow (relativeTurn c s h) := by sorry
