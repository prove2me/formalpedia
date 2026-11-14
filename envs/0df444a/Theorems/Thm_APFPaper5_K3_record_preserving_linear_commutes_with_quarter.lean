-- Prove2me | Theorems.Thm_APFPaper5_K3_record_preserving_linear_commutes_with_quarter
-- name    : APFPaper5.K3.record_preserving_linear_commutes_with_quarter
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:27:45.755473+00:00
-- url     : https://prove2.me/theorems/f64068be-5ea5-4764-b4fc-0bd411d83ae5
-- title:
--   Preserving both component costs and cross terms forces commutation with the common quarter turn
-- statement:
--   For a combo map determined by four Held2 vectors, assume pointwise preservation of recA, recB, crossRe and crossIm for every input. Then combo commutes with commonTurn 0 1 at every state. This is commutation in the supplied model, not J-module closure of a represented readout algebra.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1957'}, {'locator': '2001-2038'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_quarter_turn_commutes.lean', 'line': 114, 'declaration': 'APFPaper5.K3.record_preserving_linear_commutes_with_quarter', 'sha256': '57021aaef5be76f2f202f050063b757acfd67825da4017c90cfa00acb50027b8'}]

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

theorem APFPaper5.K3.record_preserving_linear_commutes_with_quarter (u1 u2 u3 u4 : Held2)
    (hpres : ∀ h : Held2, recA (combo u1 u2 u3 u4 h) = recA h ∧
      recB (combo u1 u2 u3 u4 h) = recB h ∧ crossRe (combo u1 u2 u3 u4 h) = crossRe h ∧
      crossIm (combo u1 u2 u3 u4 h) = crossIm h) (h : Held2) :
    commonTurn 0 1 (combo u1 u2 u3 u4 h) = combo u1 u2 u3 u4 (commonTurn 0 1 h) := by sorry
