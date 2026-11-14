-- Prove2me | Theorems.Thm_CatalyticTreeEval_Main_coefficient_evaluation_access
-- name    : CatalyticTreeEval.Main.coefficient_evaluation_access
-- status  : Open
-- author  : @sragavan
-- created : 2026-11-14T01:44:44.589218+00:00
-- url     : https://prove2.me/theorems/b7dd0854-9020-4f36-8331-a501b6082432
-- title:
--   Uniform coefficient and evaluation access from sparse polynomial printers
-- statement:
--   A single finite converter receives uniform sparse-polynomial/point printing and nonduplicated monomial enumeration. For every valid parameter string it prints the explicit coefficient vector and monomial-evaluation vector in space proportional to the supplied workspace plus the modulus bitlength. The converter may replay streams rather than storing complete monomials. This is the computational component of Lemma B.4; matching and support-coverage are not needed for the access algorithm.
-- source:
--   Henzinger, Pyne and Ragavan, Catalytic Tree Evaluation from Matching Vectors, https://arxiv.org/html/2602.14320v3, Appendix B, Lemmas B.4 and B.5.

import Definitions.Def_CatalyticTreeEval_PolynomialCoordinates

set_option autoImplicit false

namespace CatalyticTreeEval.Main

/-- The computational part of Lemma B.4, without unnecessary matching or support hypotheses. -/
theorem coefficient_evaluation_access (P : List Bool → PolySystem) (domain : Set (List Bool))
    (MP ME : Machine) (A : ℝ) (hA : 0 < A)
    (h : ∀ a ∈ domain, 1 < (P a).m ∧ 0 < (P a).s ∧
      (((P a).params a).length : ℝ) ≤ 2 ^ (A * (P a).s) ∧
      PolyFamilyAccess MP ((P a).params a) (P a).f (P a).x (A * (P a).s) ∧
      MonomialAccess ME ((P a).params a) (P a).monomials (A * (P a).s)) :
    ∃ (MV : Machine) (C : ℝ), 0 < C ∧
      ∀ a ∈ domain,
        VectorAccess MV ((P a).params a)
          (fun i => coefficientCoordinates ((P a).f i) (P a).monomials)
          (fun i => evaluationCoordinates ((P a).x i) (P a).monomials)
          (C * ((P a).s + log₂ (P a).m)) := by sorry

end CatalyticTreeEval.Main
