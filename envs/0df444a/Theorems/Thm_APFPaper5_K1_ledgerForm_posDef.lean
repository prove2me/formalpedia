-- Prove2me | Theorems.Thm_APFPaper5_K1_ledgerForm_posDef
-- name    : APFPaper5.K1.ledgerForm_posDef
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:39:11.849459+00:00
-- url     : https://prove2.me/theorems/9c797726-8cf1-47c8-9281-82bae9312794
-- title:
--   A faithful nonnegative score diagonal remains faithful after symmetrization
-- statement:
--   Let C be a supplied pairing and θ a supplied linear equivalence between its real vector-space roles. Assume hq: C(θx,x) is nonnegative for every x, and vanishes only when x=0. For the symmetric expression B(x,y)=(C(θx,y)+C(θy,x))/2, this theorem gives B(x,x)≥0 and B(x,x)=0 implies x=0. It uses the equality of the two diagonals. Bilinearity is not assumed or concluded by this declaration, and the faithful diagonal is explicitly supplied rather than derived from APF inputs.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_bilinearization.lean:62; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;312-334

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {VP VE : Type*} [AddCommGroup VP] [Module ℝ VP] [AddCommGroup VE] [Module ℝ VE]

theorem APFPaper5.K1.ledgerForm_posDef (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE)
    (hq : FaithfulNonnegDiagonal C theta) (x : VP) :
    0 ≤ ledgerForm C theta x x ∧ (ledgerForm C theta x x = 0 → x = 0) := by sorry
