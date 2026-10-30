-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991_theorem_1
-- name    : BergerSchwichtenberg1991.theorem_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T02:08:34.167346+00:00
-- url     : https://prove2.me/theorems/e7d7112d-cd6a-4f46-95eb-51f6952b462f
-- title:
--   Theorem 1: Inversion of the Evaluation Functional in Admissible Models
-- statement:
--   In any admissible model `M`, the procedure-to-expression functional `p-e_ρ` inverts evaluation on λ-definable elements and computes the long β-normal form of any closed term, yielding Strong Completeness (`M ⊨ r = s → r =_{βη} s`).
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Theorem 1 & Corollary, pp. 207-208.

import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem theorem_1 (M : AdmissibleModel.{u}) (IF : InversionFunctionals M) :
    (∀ (ρ : Ty) (a : M.Dom ρ),
      M.IsLambdaDefinable ρ a →
      ∃ t : Term,
        IF.IsPeResult ρ a t ∧
        IsClosed t ∧
        IsLongBetaNormal ρ t ∧
        ∀ η : M.Env, M.eqM ρ (M.eval t η ρ) a) ∧
    (∀ (ρ : Ty) (r rStar : Term) (θ : Substitution),
      HasType r ρ →
      HasType rStar ρ →
      IsLongBetaNormal ρ rStar →
      BetaEtaEq r rStar →
      IsWellTypedSubst θ →
      IF.IsPeResult ρ (M.eval r (IF.etaSubst θ) ρ) (EXTRACT (EMB (applySubst θ rStar))) ∧
      AlphaEq (EXTRACT (EMB (applySubst θ rStar))) (applySubst θ rStar)) ∧
    (∀ (ρ : Ty) (r s : Term),
      HasType r ρ →
      HasType s ρ →
      M.ModelsEq ρ r s →
      BetaEtaEq r s) := by sorry

end BergerSchwichtenberg1991
