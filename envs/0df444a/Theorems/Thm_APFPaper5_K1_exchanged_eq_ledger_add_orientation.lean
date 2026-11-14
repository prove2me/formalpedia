-- Prove2me | Theorems.Thm_APFPaper5_K1_exchanged_eq_ledger_add_orientation
-- name    : APFPaper5.K1.exchanged_eq_ledger_add_orientation
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:32:31.261197+00:00
-- url     : https://prove2.me/theorems/1fd00c68-0a75-4699-a9ee-6ef62ff9ece9
-- title:
--   An exchanged pairing splits into symmetric and alternating parts
-- statement:
--   Let C be any real-valued pairing on supplied terminal and preparation vector spaces, with a supplied linear equivalence θ between the roles. Put B(x,y)=(C(θx,y)+C(θy,x))/2 and A(x,y)=(C(θx,y)−C(θy,x))/2. Then C(θx,y)=B(x,y)+A(x,y) for every x,y. Neither bilinearity nor positivity is needed for this identity. It decomposes the given score, without constructing a physical score, deriving a role exchange, or identifying the symmetric part with an admissibility cost.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_bilinearization.lean:45; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;312-334

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {VP VE : Type*} [AddCommGroup VP] [Module ℝ VP] [AddCommGroup VE] [Module ℝ VE]

theorem APFPaper5.K1.exchanged_eq_ledger_add_orientation (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (x y : VP) :
    C (theta x) y = ledgerForm C theta x y + orientationForm C theta x y := by sorry
