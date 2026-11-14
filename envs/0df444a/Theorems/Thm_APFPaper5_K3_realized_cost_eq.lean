-- Prove2me | Theorems.Thm_APFPaper5_K3_realized_cost_eq
-- name    : APFPaper5.K3.realized_cost_eq
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:24:08.835583+00:00
-- url     : https://prove2.me/theorems/c9d84aff-ae29-45af-abe4-24810a42e24c
-- title:
--   Two global minimizers on the same supplied admissible set have equal prices
-- statement:
--   Let admissible be any set of states and price any real-valued function. Suppose s and t both belong to admissible and each has price no greater than every member of that same set. Then price s=price t. These two global-minimum hypotheses are explicit. This is supplied-domain optimization mathematics; identification of the domain and price with the full original A2 objects is not certified. This is a scoped reference result about the stated mathematical data and explicit hypotheses. Applying it at an original physical interface requires a separate source-faithful identification of those data; this declaration does not discharge the K3 physical realization and observable-descent obligations.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1679'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json revision 2026-10-04.1', 'locator': 'B07a'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_cost_invariant.lean', 'line': 36, 'declaration': 'APFPaper5.K3.realized_cost_eq', 'sha256': '711cb6ac43bbc199872124413291491daa432d662e5ec262c4762ec3cb7a27f1'}]

import Definitions.Def_APFPaper5_K3_Continuity

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u
variable {S : Type u}

theorem APFPaper5.K3.realized_cost_eq (admissible : Set S) (price : S → ℝ) (s t : S)
    (hs : s ∈ admissible ∧ ∀ a ∈ admissible, price s ≤ price a)
    (ht : t ∈ admissible ∧ ∀ a ∈ admissible, price t ≤ price a) : price s = price t := by sorry
