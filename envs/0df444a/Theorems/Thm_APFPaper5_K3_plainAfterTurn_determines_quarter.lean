-- Prove2me | Theorems.Thm_APFPaper5_K3_plainAfterTurn_determines_quarter
-- name    : APFPaper5.K3.plainAfterTurn_determines_quarter
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:06:03.583093+00:00
-- url     : https://prove2.me/theorems/9e4406e6-1eb3-4ca8-9013-374b43868a76
-- title:
--   Equality of designated continuation profiles determines the quarter record
-- statement:
--   If two Held2 states have equal plainAfterTurn profiles, they have equal recQuarter values. The conclusion is obtained by selecting the relative quarter-turn continuation already included in the profile definition. No hypothesis identifying that continuation with a physically admitted process is supplied.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1809-1832'}, {'locator': '2001-2038'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_direction_is_recorded.lean', 'line': 73, 'declaration': 'APFPaper5.K3.plainAfterTurn_determines_quarter', 'sha256': 'b8ae6e604389b52e7b30cb1881f7c45f662e4b9e2cbbb429b874fe114cb6a934'}]

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

theorem APFPaper5.K3.plainAfterTurn_determines_quarter (h h' : Held2)
    (hprof : plainAfterTurn h = plainAfterTurn h') : recQuarter h = recQuarter h' := by sorry
