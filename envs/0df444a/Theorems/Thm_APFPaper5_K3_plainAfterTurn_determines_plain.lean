-- Prove2me | Theorems.Thm_APFPaper5_K3_plainAfterTurn_determines_plain
-- name    : APFPaper5.K3.plainAfterTurn_determines_plain
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:05:35.860346+00:00
-- url     : https://prove2.me/theorems/18c3a804-faaa-496d-9077-1fd497062ddb
-- title:
--   Equality of designated continuation profiles determines all three plain records
-- statement:
--   If two Held2 states have equal plainAfterTurn profiles, their recA, recB and recSum values are pairwise equal. Selecting the identity relative turn from the profile gives the conclusion. The profile and its continuation family are the supplied model definitions.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1809-1832'}, {'locator': '2001-2038'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_direction_is_recorded.lean', 'line': 95, 'declaration': 'APFPaper5.K3.plainAfterTurn_determines_plain', 'sha256': 'b8ae6e604389b52e7b30cb1881f7c45f662e4b9e2cbbb429b874fe114cb6a934'}]

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

theorem APFPaper5.K3.plainAfterTurn_determines_plain (h h' : Held2)
    (hprof : plainAfterTurn h = plainAfterTurn h') :
    recA h = recA h' ∧ recB h = recB h' ∧ recSum h = recSum h' := by sorry
