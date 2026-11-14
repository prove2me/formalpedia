-- Prove2me | Theorems.Thm_APFPaper5_K3_profile_preserving_linear_commutes_with_quarter
-- name    : APFPaper5.K3.profile_preserving_linear_commutes_with_quarter
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:33:54.249994+00:00
-- url     : https://prove2.me/theorems/017ca16e-8229-4329-9a13-67868d96ef76
-- title:
--   Coordinate-linear maps preserving the designated continuation profile commute with the common quarter turn
-- statement:
--   Fix four Held2 vectors u1,u2,u3,u4 defining combo. Assume plainAfterTurn(combo u1 u2 u3 u4 h)=plainAfterTurn h for every state h. Then combo commutes pointwise with commonTurn 0 1. The universal profile-preservation hypothesis yields preservation of both component costs and both cross terms. The conclusion is commutation for this explicit map family, not generator completeness or J-module closure of a represented readout algebra. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1809-1832'}, {'locator': '2001-2038'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_direction_is_recorded.lean', 'line': 109, 'declaration': 'APFPaper5.K3.profile_preserving_linear_commutes_with_quarter', 'sha256': 'b8ae6e604389b52e7b30cb1881f7c45f662e4b9e2cbbb429b874fe114cb6a934'}]

import Definitions.Def_APFPaper5_K3_ContinuationProfile
import Definitions.Def_APF_B01_DeclaredInput
import Theorems.Thm_APFPaper5_K3_record_preserving_linear_is_common_turn
import Theorems.Thm_APFPaper5_K3_record_preserving_linear_commutes_with_quarter
import Theorems.Thm_APFPaper5_K3_rateFlip_seen_by_quarter_record
import Theorems.Thm_APFPaper5_K3_rateFlip_does_not_commute
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.profile_preserving_linear_commutes_with_quarter (u1 u2 u3 u4 : Held2)
    (hprof : ∀ h : Held2, plainAfterTurn (combo u1 u2 u3 u4 h) = plainAfterTurn h) (h : Held2) :
    commonTurn 0 1 (combo u1 u2 u3 u4 h) = combo u1 u2 u3 u4 (commonTurn 0 1 h) := by sorry
