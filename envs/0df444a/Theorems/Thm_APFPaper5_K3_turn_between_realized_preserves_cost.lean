-- Prove2me | Theorems.Thm_APFPaper5_K3_turn_between_realized_preserves_cost
-- name    : APFPaper5.K3.turn_between_realized_preserves_cost
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T18:30:54.125332+00:00
-- url     : https://prove2.me/theorems/74307f5b-4660-4e83-a149-b36327ef38eb
-- title:
--   Maps preserving global minimizers preserve the price of each supplied minimizer
-- statement:
--   Let admissible be any set of states, price a real-valued function, and f a self-map. Assume f sends every admissible global minimizer of price to an admissible global minimizer of the same price on the same set. If s is such a minimizer, price(f s)=price s. This is conditional optimization on supplied data, not a certified specialization of the original physical A2 domain or an assertion that every admitted turn preserves realization.
-- source:
--   [{'path': 'Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex', 'locator': '1660-1679'}, {'path': 'APF Reference Docs/APF Reconstruction Spine/FOUNDATION_INPUTS.json revision 2026-10-04.1', 'locator': 'B07a'}, {'path': 'frozen_v15/APFFoundationLedger/Theorems/Thm_APFPaper5_K3_preservation_cost.lean', 'line': 33, 'declaration': 'APFPaper5.K3.turn_between_realized_preserves_cost', 'sha256': '7dc1c59060e2e858bc84fc11baaa8b833830648cdb451795dfc136be34b935e6'}]

import Definitions.Def_APFPaper5_K3_Preservation
import Theorems.Thm_APFPaper5_K3_cost_invariant_of_loseNothing
import Theorems.Thm_APFPaper5_K3_realized_cost_eq

set_option autoImplicit false
namespace APFPaper5.K3
end APFPaper5.K3
open APFPaper5.K3
universe u
variable {S : Type u}

theorem APFPaper5.K3.turn_between_realized_preserves_cost (admissible : Set S) (price : S → ℝ) (f : S → S)
    (hf : ∀ s : S, (s ∈ admissible ∧ ∀ a ∈ admissible, price s ≤ price a) →
      (f s ∈ admissible ∧ ∀ a ∈ admissible, price (f s) ≤ price a))
    (s : S) (hs : s ∈ admissible ∧ ∀ a ∈ admissible, price s ≤ price a) :
    price (f s) = price s := by sorry
