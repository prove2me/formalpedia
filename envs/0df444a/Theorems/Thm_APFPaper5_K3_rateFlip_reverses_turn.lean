-- Prove2me | Theorems.Thm_APFPaper5_K3_rateFlip_reverses_turn
-- name    : APFPaper5.K3.rateFlip_reverses_turn
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-14T07:03:16.852285+00:00
-- url     : https://prove2.me/theorems/d91c483e-149d-497a-bb1b-00283ab092de
-- title:
--   Rate reversal conjugates a common turn-form map to the opposite orientation
-- statement:
--   For arbitrary real c,s and every Held2 state h, rateFlip(commonTurn c s h)=commonTurn c (−s)(rateFlip h). The orientation parameter changes sign in this exact identity. No unit condition is required; physical loop reversal is not identified with rateFlip here.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1957'}, {'locator': '2001-2038'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_quarter_turn_commutes.lean', 'line': 147, 'declaration': 'APFPaper5.K3.rateFlip_reverses_turn', 'sha256': '57021aaef5be76f2f202f050063b757acfd67825da4017c90cfa00acb50027b8'}]

import Definitions.Def_APFPaper5_K3_LinearOnTwoComponents
import Theorems.Thm_APFPaper5_K3_commonTurn_unseen
import Theorems.Thm_APFPaper5_K3_records_are_cross_data
import Theorems.Thm_APFPaper5_K3_commonQuarter_commutes_common
import Theorems.Thm_APFPaper5_K3_same_records_give_common_turn
import Theorems.Thm_APFPaper5_K3_cross_invariant_under_commonTurn
import Theorems.Thm_APFPaper5_K3_relativeTurn_keeps_own_records
import Theorems.Thm_APFPaper5_K3_relativeTurn_rotates_cross
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.rateFlip_reverses_turn (c s : ℝ) (h : Held2) :
    rateFlip (commonTurn c s h) = commonTurn c (-s) (rateFlip h) := by sorry
