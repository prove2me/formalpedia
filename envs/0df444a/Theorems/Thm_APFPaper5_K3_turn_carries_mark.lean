-- Prove2me | Theorems.Thm_APFPaper5_K3_turn_carries_mark
-- name    : APFPaper5.K3.turn_carries_mark
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:37:17.76723+00:00
-- url     : https://prove2.me/theorems/5b98b1fe-f534-458f-8df0-b341a7222e38
-- title:
--   Conjugating a parameterized mark applies the corresponding real-pair action
-- statement:
--   For arbitrary real a,b,u,v, conjugating markQ u v by turn a b and its transpose yields markQ(a u−b v)(b u+a v). No unit condition is needed for this identity. Orthogonal-turn interpretation applies only in the normalized regime.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_continuity.lean', 'line': 35, 'declaration': 'APFPaper5.K3.turn_carries_mark', 'sha256': 'ea4710cba177600c35eab6a4e36f0d66fb184af59ae4b643f911dd5376aa58ba'}]

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

theorem APFPaper5.K3.turn_carries_mark (a b u v : ℝ) :
    mul (mul (turn a b) (markQ u v)) (tr (turn a b)) = markQ (a * u - b * v) (b * u + a * v) := by sorry
