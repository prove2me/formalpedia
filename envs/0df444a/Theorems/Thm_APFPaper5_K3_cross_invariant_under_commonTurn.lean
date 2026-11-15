-- Prove2me | Theorems.Thm_APFPaper5_K3_cross_invariant_under_commonTurn
-- name    : APFPaper5.K3.cross_invariant_under_commonTurn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T06:31:10.652872+00:00
-- url     : https://prove2.me/theorems/ae213ed9-a5a7-4404-ae2e-224d96d062fb
-- title:
--   Common unit turns preserve both model cross terms
-- statement:
--   For real c,s satisfying c²+s²=1 and every Held2 state h, applying commonTurn c s leaves both crossRe h and crossIm h unchanged. The unit equation is explicit and necessary for the stated invariance of these supplied bilinear expressions.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1621-1649'}, {'locator': '1809-1832'}, {'locator': '1957'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_components.lean', 'line': 55, 'declaration': 'APFPaper5.K3.cross_invariant_under_commonTurn', 'sha256': 'f24f1e3f6eb86f0848b62f865fa28c02e83e823ebc1f0921a0b37cce25f85af9'}]

import Definitions.Def_APFPaper5_K3_TwoComponents
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.cross_invariant_under_commonTurn (c s : ℝ) (hcs : c * c + s * s = 1) (h : Held2) :
    crossRe (commonTurn c s h) = crossRe h ∧ crossIm (commonTurn c s h) = crossIm h := by sorry
