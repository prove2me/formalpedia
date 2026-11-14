-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_polynomial_matching_coordinates
-- name    : CatalyticTreeEval.Main.polynomial_matching_coordinates
-- status  : Proved
-- author  : @sragavan
-- created : 2026-11-14T01:33:55.776845+00:00
-- url     : https://prove2.me/theorems/ec60847a-b1b3-404d-81ef-330224d83b70
-- title:
--   Polynomial matching families yield coefficient-evaluation matching vectors
-- statement:
--   Let a finite family of multivariate polynomials and points be a polynomial matching family over the residue ring. Fix a list of monomials with no repetitions which covers every polynomial support. Coefficient vectors and monomial-evaluation vectors indexed by this list form a matching-vector family with score set enlarged by zero. Their dimension is exactly the length of the list. This is the algebraic component of Lemma B.4; uniform machine access remains a separate obligation.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemma B.4.

import Definitions.Def_CatalyticTreeEval_PolynomialCoordinates
open CatalyticTreeEval.Main
set_option autoImplicit false

theorem CatalyticTreeEval.Main.polynomial_matching_coordinates {m H N : ℕ} (S₀ : Set (ZMod m))
    (f : Fin N → Poly m H) (x : Fin N → Vec m H) (ms : List (Monomial H))
    (hmatching : PolyMatching S₀ f x) (hnodup : ms.Nodup)
    (hcover : ∀ i, ∀ v ∈ (f i).support, v ∈ ms) :
    SMatching (S₀ ∪ {0})
      (fun i => coefficientCoordinates (f i) ms)
      (fun i => evaluationCoordinates (x i) ms) := by sorry
