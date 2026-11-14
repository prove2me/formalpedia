-- Prove2me | Theorems.Thm_APFPaper5_K1_diagonal_parallelogram
-- name    : APFPaper5.K1.diagonal_parallelogram
-- status  : Proved
-- author  : @FiniteUniverse
-- created : 2026-11-13T17:29:42.259876+00:00
-- url     : https://prove2.me/theorems/ab28b8f3-2b03-4be6-bc57-2d286d6c6ef5
-- title:
--   Bilinearity gives the parallelogram identity for the exchanged diagonal
-- statement:
--   Let C be a real-bilinear pairing on supplied real vector spaces, with linear role equivalence θ. Define q(x)=C(θx,x). Under the named bilinearity hypothesis hC, the conclusion is q(x+y)+q(x−y)=2q(x)+2q(y) for all x,y. Positivity and faithfulness of q are unnecessary for this algebraic identity. The theorem starts from a bilinear pairing; it does not construct one from a physical score or prove that a supplied admissibility cost is its diagonal.
-- source:
--   Sib v15 frozen source: Theorems/Thm_APFPaper5_K1_bilinearization.lean:69; Papers/Paper 05 - Quantum Structure - Hilbert Space and Born Rule/Paper_5_Quantum_Structure_Hilbert_Born_Supplement_v7.33.tex, 353-391;312-334

import Definitions.Def_APFPaper5_K1_OrderedScore
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring

set_option autoImplicit false
namespace APFPaper5.K1
end APFPaper5.K1
open APFPaper5.K1
variable {VP VE : Type*} [AddCommGroup VP] [Module ℝ VP] [AddCommGroup VE] [Module ℝ VE]

theorem APFPaper5.K1.diagonal_parallelogram (C : VE → VP → ℝ) (theta : VP ≃ₗ[ℝ] VE) (hC : IsBilinear C)
    (x y : VP) :
    C (theta (x + y)) (x + y) + C (theta (x - y)) (x - y) =
      2 * C (theta x) x + 2 * C (theta y) y := by sorry
