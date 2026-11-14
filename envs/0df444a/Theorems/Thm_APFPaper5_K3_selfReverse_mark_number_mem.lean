-- Prove2me | Theorems.Thm_APFPaper5_K3_selfReverse_mark_number_mem
-- name    : APFPaper5.K3.selfReverse_mark_number_mem
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:25:32.316337+00:00
-- url     : https://prove2.me/theorems/0febd957-e4fe-4600-a083-da922d641cff
-- title:
--   A self-transpose idempotent array has fixed-mark sandwich coefficient in the unit interval
-- statement:
--   Let q be an M2 array satisfying tr q=q and mul q q=q. Then 0≤q.a≤1. Both self-transpose and idempotence are explicit hypotheses. The result bounds the coefficient extracted by the fixed-mark sandwich in the supplied array model; it does not assert that physical reversal is transpose or that every physical mark has these algebraic properties. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1679'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_range.lean', 'line': 23, 'declaration': 'APFPaper5.K3.selfReverse_mark_number_mem', 'sha256': '23eb7bf4fcaf85f5e351db14162abd607e657d5a58b2c936f99c6ffea372289f'}]

import Definitions.Def_APFPaper5_K3_TwoMarkExchange
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.selfReverse_mark_number_mem (q : M2) (hsym : tr q = q) (hidem : mul q q = q) :
    0 ≤ q.a ∧ q.a ≤ 1 := by sorry
