-- Prove2me | Theorems.Thm_APFPaper5_K3_crossTerm_turn_invariant
-- name    : APFPaper5.K3.crossTerm_turn_invariant
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:21:04.516386+00:00
-- url     : https://prove2.me/theorems/20add3e0-b22f-4d3b-a6e6-d3e9a7b7b55d
-- title:
--   Simultaneous conjugation by a unit turn preserves the chosen cross term
-- statement:
--   For real a,b satisfying a²+b²=1 and any M2 arrays x,y, conjugating both by turn a b and its transpose leaves crossTerm x y unchanged. The claim concerns the specified entrywise bilinear pairing and simultaneous action on both arguments. It does not supply a physical ordered-score construction, show that every record has this form, or establish original admission of the model turns. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '271-350'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_cross_term.lean', 'line': 58, 'declaration': 'APFPaper5.K3.crossTerm_turn_invariant', 'sha256': '00278a46a28a7186d0f5ef435bceb8d2c6a71efd53d03dbc25f8aa6d924daa72'}]

import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.crossTerm_turn_invariant (a b : ℝ) (h : a * a + b * b = 1) (x y : M2) :
    crossTerm (mul (mul (turn a b) x) (tr (turn a b))) (mul (mul (turn a b) y) (tr (turn a b))) =
      crossTerm x y := by sorry
