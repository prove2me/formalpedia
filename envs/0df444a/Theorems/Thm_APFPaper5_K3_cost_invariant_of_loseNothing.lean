-- Prove2me | Theorems.Thm_APFPaper5_K3_cost_invariant_of_loseNothing
-- name    : APFPaper5.K3.cost_invariant_of_loseNothing
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:20:12.629043+00:00
-- url     : https://prove2.me/theorems/fb6247ac-8117-4fc8-98b3-fd49554d58c8
-- title:
--   Admitted reversible nonincreasing maps preserve a supplied real cost
-- statement:
--   For a supplied set Adm of self-maps on S, assume every admitted map has an admitted left inverse and every admitted map weakly decreases the real-valued cost at every state. Then every admitted map preserves cost exactly at every state. The reverse inequality follows by applying nonincrease to its admitted inverse. Neither reversibility nor nonincrease is derived here from foundation inputs. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1679'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json revision 2026-10-04.1', 'locator': 'B07a'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_cost_invariant.lean', 'line': 26, 'declaration': 'APFPaper5.K3.cost_invariant_of_loseNothing', 'sha256': '711cb6ac43bbc199872124413291491daa432d662e5ec262c4762ec3cb7a27f1'}]

import Definitions.Def_APFPaper5_K3_Continuity

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u
variable {S : Type u}

theorem APFPaper5.K3.cost_invariant_of_loseNothing (Adm : Set (S → S)) (h : TurnsLoseNothing Adm)
    (cost : S → ℝ) (hnoraise : ∀ f ∈ Adm, ∀ s : S, cost (f s) ≤ cost s) :
    ∀ f ∈ Adm, ∀ s : S, cost (f s) = cost s := by sorry
