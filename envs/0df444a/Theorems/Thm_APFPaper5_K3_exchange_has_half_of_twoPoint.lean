-- Prove2me | Theorems.Thm_APFPaper5_K3_exchange_has_half_of_twoPoint
-- name    : APFPaper5.K3.exchange_has_half_of_twoPoint
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:45:25.101145+00:00
-- url     : https://prove2.me/theorems/fe1648e0-0667-4733-9a07-9f417b898791
-- title:
--   Two-point transitivity and admitted square roots give an exchange performed by a turn twice
-- statement:
--   For supplied Marks, score B and admitted self-maps Adm, assume symmetry of B, TwoPoint Marks B Adm and TurnsHaveHalves Adm. For any p,q in Marks, an H in Adm satisfies H(H p)=q and H(H q)=p. The hypotheses provide both pair transitivity and square roots of admitted maps. No foundation input is claimed to supply either candidate clause. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '3037-3056'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_exchange_test.lean', 'line': 43, 'declaration': 'APFPaper5.K3.exchange_has_half_of_twoPoint', 'sha256': '8a82f1783d2b08f2df6bb6c9fd29f7e6c2bfc94e3196bc72c4266df6c0e4639e'}]

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

theorem APFPaper5.K3.exchange_has_half_of_twoPoint {V : Type u} (Marks : Set V) (B : V → V → ℝ)
    (Adm : Set (V → V)) (hsymm : ∀ p q : V, B p q = B q p) (h : TwoPoint Marks B Adm)
    (hh : TurnsHaveHalves Adm) (p q : V) (hp : p ∈ Marks) (hq : q ∈ Marks) :
    ∃ H ∈ Adm, H (H p) = q ∧ H (H q) = p := by sorry
