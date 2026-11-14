-- Prove2me | Theorems.Thm_APFPaper5_K3_plane_no_turn_exchanges_between
-- name    : APFPaper5.K3.plane_no_turn_exchanges_between
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:52:15.947299+00:00
-- url     : https://prove2.me/theorems/c51c580b-18bf-49bd-9919-30fe184520f4
-- title:
--   No turn-form array exchanges the fixed mark with the halfway mark
-- statement:
--   Let r be a real number with 2r²=1. There are no real a,b such that conjugation by turn a b sends markP to markQ r r and also sends markQ r r back to markP. The claim covers every real pair a,b, even without a unit restriction. It is an obstruction in the supplied plane model, not a full independence theorem for all foundation or K-layer clauses. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '3037-3056'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_exchange_test.lean', 'line': 61, 'declaration': 'APFPaper5.K3.plane_no_turn_exchanges_between', 'sha256': '8a82f1783d2b08f2df6bb6c9fd29f7e6c2bfc94e3196bc72c4266df6c0e4639e'}]

import Definitions.Def_APFPaper5_K3_TwoPoint
import Definitions.Def_APFPaper5_K3_TwoMarkCost
import Theorems.Thm_APFPaper5_K3_turn_carries_mark
import Theorems.Thm_APFPaper5_K3_twoMark_continuity
import Theorems.Thm_APFPaper5_K3_strictly_between_iff_not_commute
import Theorems.Thm_APFPaper5_K3_pair_number_is_cross_term
import Theorems.Thm_APFPaper5_K3_sqCost_turn_invariant
import Theorems.Thm_APFPaper5_K3_crossTerm_turn_invariant
import Theorems.Thm_APFPaper5_K3_no_turn_exchanges
import Theorems.Thm_APFPaper5_K3_slant_pqp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u

theorem APFPaper5.K3.plane_no_turn_exchanges_between (r : ℝ) (hr : 2 * (r * r) = 1) :
    ¬ ∃ a b : ℝ, mul (mul (turn a b) markP) (tr (turn a b)) = markQ r r ∧
      mul (mul (turn a b) (markQ r r)) (tr (turn a b)) = markP := by sorry
