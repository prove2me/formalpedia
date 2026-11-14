-- Prove2me | Theorems.Thm_APFPaper5_K3_cost_invariant_of_preservation
-- name    : APFPaper5.K3.cost_invariant_of_preservation
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:30:26.553558+00:00
-- url     : https://prove2.me/theorems/b5dbc8bd-1f91-4456-9afb-2918b3cad0db
-- title:
--   The named reversible and nonincrease hypotheses imply exact cost preservation
-- statement:
--   For a supplied set Adm of self-maps on S and cost:S→ℝ, assume TurnsLoseNothing Adm and TurnsNeverRaiseCost Adm cost. Then every f in Adm preserves cost at every state. This theorem restates the inverse/nonincrease argument using the two named predicates. Their status is explicit K-layer hypotheses; the declaration does not derive them from the adopted foundation or identify cost with an original physical ledger. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1679'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json revision 2026-10-04.1', 'locator': 'B07a'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_preservation_cost.lean', 'line': 28, 'declaration': 'APFPaper5.K3.cost_invariant_of_preservation', 'sha256': '7dc1c59060e2e858bc84fc11baaa8b833830648cdb451795dfc136be34b935e6'}]

import Definitions.Def_APFPaper5_K3_Preservation
import Theorems.Thm_APFPaper5_K3_cost_invariant_of_loseNothing
import Theorems.Thm_APFPaper5_K3_realized_cost_eq

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u
variable {S : Type u}

theorem APFPaper5.K3.cost_invariant_of_preservation (Adm : Set (S → S)) (cost : S → ℝ)
    (h : TurnsLoseNothing Adm) (hc : TurnsNeverRaiseCost Adm cost) :
    ∀ f ∈ Adm, ∀ s : S, cost (f s) = cost s := by sorry
