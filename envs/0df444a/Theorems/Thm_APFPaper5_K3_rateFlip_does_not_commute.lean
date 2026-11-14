-- Prove2me | Theorems.Thm_APFPaper5_K3_rateFlip_does_not_commute
-- name    : APFPaper5.K3.rateFlip_does_not_commute
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:27:26.579206+00:00
-- url     : https://prove2.me/theorems/b06d23d4-7b2e-4e98-8fc6-c3644b3fb0fc
-- title:
--   A concrete state witnesses failure of rate flip to commute with the common quarter turn
-- statement:
--   At the Held2 state (1,0,0,0), applying rateFlip and commonTurn 0 1 in opposite orders produces unequal states. This is a concrete noncommutation witness for the supplied polynomial maps. Together with separately stated record identities it can serve as a control, but this declaration alone does not identify physical reversal, monodromy or admission and does not establish failure of a physical observable-descent condition. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1957'}, {'locator': '2001-2038'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_quarter_turn_commutes.lean', 'line': 140, 'declaration': 'APFPaper5.K3.rateFlip_does_not_commute', 'sha256': '57021aaef5be76f2f202f050063b757acfd67825da4017c90cfa00acb50027b8'}]

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

theorem APFPaper5.K3.rateFlip_does_not_commute :
    commonTurn 0 1 (rateFlip ⟨1, 0, 0, 0⟩) ≠ rateFlip (commonTurn 0 1 ⟨1, 0, 0, 0⟩) := by sorry
