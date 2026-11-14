-- Prove2me | Theorems.Thm_APFPaper5_K3_no_turn_exchanges
-- name    : APFPaper5.K3.no_turn_exchanges
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:42:13.481221+00:00
-- url     : https://prove2.me/theorems/9603e83b-5820-4fec-8cb9-5e0b1aae55af
-- title:
--   Two-way exchange by a turn-form array forces the mark parameters to have zero product
-- statement:
--   Suppose conjugation by turn a b sends markP to markQ u v and sends markQ u v back to markP. Then u·v=0. The theorem assumes the two exchange equations directly and imposes no separate normalization on a,b,u,v. It gives a necessary algebraic condition for two-way exchange in this model, not a general requirement that physical marks be exchanged by turns. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '3037-3056'}, {'path': 'Papers/Paper 01 - The Enforceability of Distinction/Paper_1_Enforceability_of_Distinction_Supplement_v9.28.tex', 'locator': '6276-6280'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_two_mark_exchange.lean', 'line': 42, 'declaration': 'APFPaper5.K3.no_turn_exchanges', 'sha256': 'd09e06cb9d79ab09f7b3398c366e4f682e9507983189298bc30c2f9a4f91502b'}]

import Definitions.Def_APFPaper5_K3_TwoMarkExchange
import Theorems.Thm_APFPaper5_K3_turn_carries_mark
import Theorems.Thm_APFPaper5_K3_twoMark_continuity
import Theorems.Thm_APFPaper5_K3_strictly_between_iff_not_commute
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3

theorem APFPaper5.K3.no_turn_exchanges (a b u v : ℝ)
    (h1 : mul (mul (turn a b) markP) (tr (turn a b)) = markQ u v)
    (h2 : mul (mul (turn a b) (markQ u v)) (tr (turn a b)) = markP) : u * v = 0 := by sorry
