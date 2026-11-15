-- Prove2me | Theorems.Thm_APFPaper5_K3_relativeTurn_rotates_cross
-- name    : APFPaper5.K3.relativeTurn_rotates_cross
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:59:28.348885+00:00
-- url     : https://prove2.me/theorems/c43fce64-c03d-455b-96ea-767439238b5a
-- title:
--   Relative turn-form maps transform the two cross terms by an explicit rotation-form law
-- statement:
--   For arbitrary real c,s and every Held2 state, the new crossRe is c crossRe+s crossIm, while the new crossIm is c crossIm−s crossRe. The theorem is this pair of polynomial identities; the parameters are not required to be a unit pair.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1649'}, {'locator': '1809-1832'}, {'locator': '1957'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_components.lean', 'line': 74, 'declaration': 'APFPaper5.K3.relativeTurn_rotates_cross', 'sha256': 'f24f1e3f6eb86f0848b62f865fa28c02e83e823ebc1f0921a0b37cce25f85af9'}]

import Definitions.Def_APFPaper5_K3_TwoComponents
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.relativeTurn_rotates_cross (c s : ℝ) (h : Held2) :
    crossRe (relativeTurn c s h) = c * crossRe h + s * crossIm h ∧
      crossIm (relativeTurn c s h) = c * crossIm h - s * crossRe h := by sorry
