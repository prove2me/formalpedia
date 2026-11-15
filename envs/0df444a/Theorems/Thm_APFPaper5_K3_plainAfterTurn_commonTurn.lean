-- Prove2me | Theorems.Thm_APFPaper5_K3_plainAfterTurn_commonTurn
-- name    : APFPaper5.K3.plainAfterTurn_commonTurn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:05:39.259608+00:00
-- url     : https://prove2.me/theorems/ee658986-6f15-48ce-a0e8-8ee9b7f47983
-- title:
--   Common unit turns preserve the designated relative-turn continuation profile
-- statement:
--   If c²+s²=1, applying commonTurn c s to any Held2 state leaves plainAfterTurn unchanged as a predicate-valued profile. That profile is defined using all unit-pair relative turns and the three plain model records. The theorem uses this designated continuation family, not an inferred original-ledger admission relation.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1809-1832'}, {'locator': '2001-2038'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_direction_is_recorded.lean', 'line': 65, 'declaration': 'APFPaper5.K3.plainAfterTurn_commonTurn', 'sha256': 'b8ae6e604389b52e7b30cb1881f7c45f662e4b9e2cbbb429b874fe114cb6a934'}]

import Definitions.Def_APFPaper5_K3_ContinuationProfile
import Definitions.Def_APF_B01_DeclaredInput
import Theorems.Thm_APFPaper5_K3_record_preserving_linear_is_common_turn
import Theorems.Thm_APFPaper5_K3_record_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFPaper5_K3_rateFlip_seen_by_quarter_record
import Theorems.Thm_APFPaper5_K3_rateFlip_does_not_commute
import Theorems.Thm_APFPaper5_K3_rateFlip_preserves_plain_records
import Theorems.Thm_APFPaper5_K3_rateFlip_reverses_turn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.plainAfterTurn_commonTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    plainAfterTurn (commonTurn c s h) = plainAfterTurn h := by sorry
