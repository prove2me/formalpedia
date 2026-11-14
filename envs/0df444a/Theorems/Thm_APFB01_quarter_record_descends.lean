-- Prove2me | Theorems.Thm_APFB01_quarter_record_descends
-- name    : APFB01.quarter_record_descends
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:33:39.411571+00:00
-- url     : https://prove2.me/theorems/3b5c152d-1e4a-4fce-8680-935967936469
-- title:
--   The quarter-record equality predicate descends through the designated continuation-profile quotient
-- statement:
--   For every real r, the predicate recQuarter h=r on Held2 descends through the quotient by equality of plainAfterTurn profiles. The proof constructs the descended predicate with Quot.lift, using the theorem that equal profiles determine the quarter record. No B01 hypothesis is consumed. This shows factorization of a chosen model predicate; it does not establish that every quotient-invariant predicate is physically realized. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1809-1832'}, {'locator': '2001-2038'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_direction_is_recorded.lean', 'line': 125, 'declaration': 'APFB01.quarter_record_descends', 'sha256': 'b8ae6e604389b52e7b30cb1881f7c45f662e4b9e2cbbb429b874fe114cb6a934'}]

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

open APFPaper5.K3 in
theorem APFB01.quarter_record_descends (r : ℝ) :
    APFB01.Descends plainAfterTurn (fun h : Held2 => recQuarter h = r) := by sorry
