-- Prove2me | Theorems.Thm_APFPaper5_K3_twoMark_continuity
-- name    : APFPaper5.K3.twoMark_continuity
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:40:21.787946+00:00
-- url     : https://prove2.me/theorems/28a57dc0-3eda-4b2e-97d4-fc2fdea999f8
-- title:
--   The unit-pair model satisfies the three designated continuity clauses under explicit real-root existence
-- statement:
--   Assume every nonnegative real number has a real square root. Then Continuity relNumber 0 1 admTurns holds: the number attains the full unit interval, an admitted model turn reaches every such number from every state, and every admitted model turn has an admitted left inverse. These are the three defined clauses; no topological continuity, smooth Lie-image condition or original physical admission theorem is established. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_continuity.lean', 'line': 97, 'declaration': 'APFPaper5.K3.twoMark_continuity', 'sha256': 'ea4710cba177600c35eab6a4e36f0d66fb184af59ae4b643f911dd5376aa58ba'}]

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

theorem APFPaper5.K3.twoMark_continuity (hroot : ∀ t : ℝ, 0 ≤ t → ∃ r : ℝ, r * r = t) :
    Continuity relNumber 0 1 admTurns := by sorry
