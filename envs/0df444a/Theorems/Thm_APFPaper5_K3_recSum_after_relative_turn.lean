-- Prove2me | Theorems.Thm_APFPaper5_K3_recSum_after_relative_turn
-- name    : APFPaper5.K3.recSum_after_relative_turn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:11:06.492208+00:00
-- url     : https://prove2.me/theorems/e32b29f5-a016-48fe-b1e4-82504efaf249
-- title:
--   Plain recombination after a relative turn expands into costs and cross terms
-- statement:
--   For arbitrary real c,s and every Held2 state, recSum after relativeTurn c s equals recA+(c²+s²)recB+2(c crossRe+s crossIm), evaluated at the original state. No unit equation is required for this exact polynomial expansion of the supplied record formulas.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1809-1832'}, {'locator': '2001-2038'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '1054-1066'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_direction_is_recorded.lean', 'line': 45, 'declaration': 'APFPaper5.K3.recSum_after_relative_turn', 'sha256': 'b8ae6e604389b52e7b30cb1881f7c45f662e4b9e2cbbb429b874fe114cb6a934'}]

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

theorem APFPaper5.K3.recSum_after_relative_turn (c s : ℝ) (h : Held2) :
    recSum (relativeTurn c s h) =
      recA h + (c * c + s * s) * recB h + 2 * (c * crossRe h + s * crossIm h) := by sorry
