-- Prove2me | Theorems.Thm_APFPaper5_K3_strictly_between_iff_not_commute
-- name    : APFPaper5.K3.strictly_between_iff_not_commute
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:37:07.320887+00:00
-- url     : https://prove2.me/theorems/062d5d4a-d42a-4735-b631-181e6463315a
-- title:
--   Strictly intermediate unit-pair numbers are exactly the noncommuting fixed/turned mark pairs
-- statement:
--   For every UnitPair w, its designated relation number is strictly between zero and one if and only if markP and markOf w do not commute under the explicit M2 multiplication. UnitPair supplies normalization and markOf is the chosen projection formula. This result classifies the supplied model pairs; it does not establish that any original physical interface realizes a noncommuting pair or a continuum of such numbers. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_continuity.lean', 'line': 130, 'declaration': 'APFPaper5.K3.strictly_between_iff_not_commute', 'sha256': 'ea4710cba177600c35eab6a4e36f0d66fb184af59ae4b643f911dd5376aa58ba'}]

import Definitions.Def_APFPaper5_K3_Continuity
import Definitions.Def_APFPaper5_K3_TwoMarkStates
import Theorems.Thm_APFPaper5_K3_pqp
import Theorems.Thm_APFPaper5_K3_turn_carries
import Theorems.Thm_APFPaper5_K3_turn_inverse
import Theorems.Thm_APFPaper5_K3_turn_compose
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.strictly_between_iff_not_commute (w : UnitPair) :
    (0 < relNumber w ∧ relNumber w < 1) ↔ mul markP (markOf w) ≠ mul (markOf w) markP := by sorry
