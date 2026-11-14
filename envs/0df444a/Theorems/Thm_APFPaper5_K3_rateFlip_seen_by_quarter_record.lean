-- Prove2me | Theorems.Thm_APFPaper5_K3_rateFlip_seen_by_quarter_record
-- name    : APFPaper5.K3.rateFlip_seen_by_quarter_record
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:27:35.629318+00:00
-- url     : https://prove2.me/theorems/154d1cfb-5b1e-48e6-9a8b-6d5e634bc343
-- title:
--   The quarter record changes from zero to four under one explicit rate flip
-- statement:
--   At the Held2 state (1,0,0,1), recQuarter is zero, whereas recQuarter of its rate flip is four. This supplies a concrete witness that the chosen quarter record detects rateFlip. It is a model calculation, not a physical implementation claim.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1957'}, {'locator': '2001-2038'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_quarter_turn_commutes.lean', 'line': 132, 'declaration': 'APFPaper5.K3.rateFlip_seen_by_quarter_record', 'sha256': '57021aaef5be76f2f202f050063b757acfd67825da4017c90cfa00acb50027b8'}]

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

theorem APFPaper5.K3.rateFlip_seen_by_quarter_record :
    recQuarter ⟨1, 0, 0, 1⟩ = 0 ∧ recQuarter (rateFlip ⟨1, 0, 0, 1⟩) = 4 := by sorry
