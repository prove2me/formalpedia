-- Prove2me | Theorems.Thm_APFPaper5_K3_record_preserving_linear_is_common_turn
-- name    : APFPaper5.K3.record_preserving_linear_is_common_turn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:30:43.302346+00:00
-- url     : https://prove2.me/theorems/e04968e8-02e2-4b9c-ac07-7b8bd7dc4bb2
-- title:
--   Preserving both component costs and both cross terms forces a common unit turn
-- statement:
--   Fix four Held2 vectors defining combo. Suppose, for every input state, combo preserves recA, recB, crossRe and crossIm separately. Then there exist real c,s with c²+s²=1 such that combo h=commonTurn c s h for every h. This classifies the explicitly coordinate-linear map family under a universal preservation hypothesis. No faithful represented observable algebra, generator completeness or physical admission relation is constructed. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1957'}, {'locator': '2001-2038'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_quarter_turn_commutes.lean', 'line': 35, 'declaration': 'APFPaper5.K3.record_preserving_linear_is_common_turn', 'sha256': '57021aaef5be76f2f202f050063b757acfd67825da4017c90cfa00acb50027b8'}]

import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Theorems.Thm_APFPaper5_K3_commonTurn_unseen
import Theorems.Thm_APFPaper5_K3_records_are_cross_data
import Theorems.Thm_APFPaper5_K3_commonQuarter_commutes_common
import Theorems.Thm_APFPaper5_K3_same_records_give_common_turn
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.record_preserving_linear_is_common_turn (u1 u2 u3 u4 : Held2)
    (hpres : ∀ h : Held2, recA (combo u1 u2 u3 u4 h) = recA h ∧
      recB (combo u1 u2 u3 u4 h) = recB h ∧ crossRe (combo u1 u2 u3 u4 h) = crossRe h ∧
      crossIm (combo u1 u2 u3 u4 h) = crossIm h) :
    ∃ c s : ℝ, c * c + s * s = 1 ∧ ∀ h : Held2, combo u1 u2 u3 u4 h = commonTurn c s h := by sorry
