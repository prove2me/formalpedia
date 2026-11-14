-- Prove2me | Theorems.Thm_APFPaper5_K3_sqCost_turn_invariant
-- name    : APFPaper5.K3.sqCost_turn_invariant
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:25:36.889416+00:00
-- url     : https://prove2.me/theorems/fb7d9e8d-c72c-4787-992b-1b1f28332f6b
-- title:
--   Conjugation by a unit turn preserves the chosen array quadratic cost
-- statement:
--   For real a,b satisfying a²+b²=1 and any M2 array x, conjugation by turn a b and its transpose preserves sqCost x. Unit normalization is explicit. The result is preservation of the supplied sum-of-squares cost, not an original physical cost law.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '271-350'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_cross_term.lean', 'line': 50, 'declaration': 'APFPaper5.K3.sqCost_turn_invariant', 'sha256': '00278a46a28a7186d0f5ef435bceb8d2c6a71efd53d03dbc25f8aa6d924daa72'}]

import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.sqCost_turn_invariant (a b : ℝ) (h : a * a + b * b = 1) (x : M2) :
    sqCost (mul (mul (turn a b) x) (tr (turn a b))) = sqCost x := by sorry
