-- Prove2me | Theorems.Thm_APFPaper5_K3_relativeTurn_one_zero
-- name    : APFPaper5.K3.relativeTurn_one_zero
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:12:13.762536+00:00
-- url     : https://prove2.me/theorems/5d68bc50-9f07-4b1e-a22c-97aa9e5fb94e
-- title:
--   The relative turn with parameters one and zero is the identity
-- statement:
--   For every Held2 state h, relativeTurn 1 0 h=h. The definition leaves the first component unchanged and acts as the identity on the second component at these parameters. This is an arithmetic helper for recovering the unturned model records from a continuation profile.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1809-1832'}, {'locator': '2001-2038'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_direction_is_recorded.lean', 'line': 92, 'declaration': 'APFPaper5.K3.relativeTurn_one_zero', 'sha256': 'b8ae6e604389b52e7b30cb1881f7c45f662e4b9e2cbbb429b874fe114cb6a934'}]

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

theorem APFPaper5.K3.relativeTurn_one_zero (h : Held2) : relativeTurn 1 0 h = h := by sorry
