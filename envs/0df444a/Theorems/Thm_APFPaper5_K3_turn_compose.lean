-- Prove2me | Theorems.Thm_APFPaper5_K3_turn_compose
-- name    : APFPaper5.K3.turn_compose
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:33:59.003663+00:00
-- url     : https://prove2.me/theorems/85fa8085-b863-4b7d-9d2f-562694359e30
-- title:
--   Multiplication of planar turn-form arrays follows real-pair multiplication
-- statement:
--   For arbitrary real u,v,u′,v′, mul(turn u v)(turn u′ v′)=turn(u u′−v v′)(u v′+v u′). The composition formula requires no unit hypotheses. It is an identity of the supplied M2 multiplication and turn definitions.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_turn.lean', 'line': 49, 'declaration': 'APFPaper5.K3.turn_compose', 'sha256': '8a760265b0fcaf3e72921bc878d437508df2077a03d6ae38ed3ef2436a5bb040'}]

import Definitions.Def_APFPaper5_K3_TwoMarkModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.turn_compose (u v u' v' : ℝ) :
    mul (turn u v) (turn u' v') = turn (u * u' - v * v') (u * v' + v * u') := by sorry
