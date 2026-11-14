-- Prove2me | Theorems.Thm_APFPaper5_K3_turn_carries
-- name    : APFPaper5.K3.turn_carries
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:30:56.376481+00:00
-- url     : https://prove2.me/theorems/6c99d85e-171c-41de-8e9d-a9f98c707a8c
-- title:
--   The planar turn-form array sends the fixed mark to the parameterized mark by conjugation
-- statement:
--   For arbitrary real u,v, conjugating markP by turn u v and its transpose yields markQ u v. The identity holds without normalization. Orthogonality and reversibility as a unit turn require the separate unit-pair hypothesis used in other declarations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1686-1717'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_turn.lean', 'line': 43, 'declaration': 'APFPaper5.K3.turn_carries', 'sha256': '8a760265b0fcaf3e72921bc878d437508df2077a03d6ae38ed3ef2436a5bb040'}]

import Definitions.Def_APFPaper5_K3_TwoMarkModel
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.turn_carries (u v : ℝ) : mul (mul (turn u v) markP) (tr (turn u v)) = markQ u v := by sorry
