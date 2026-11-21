-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991V2_theorem_1
-- name    : BergerSchwichtenberg1991V2.theorem_1
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:14:52.107302+00:00
-- url     : https://prove2.me/theorems/f283b809-f317-4646-97da-a50b60fbe8d7
-- title:
--   Theorem 1 — Inversion, normalization, and admissible-model completeness
-- statement:
--   The inversion term of an admissible model inverts closed denotations and gives closed long normal representatives. In a typed substitution environment it returns an $\alpha$-variant of the result of substituting into a long $\beta$-normal form of the original term. Equality in all environments entails $\beta\eta$-convertibility.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Theorem 1, pp. 207–208. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Models

namespace BergerSchwichtenberg1991V2

universe u

/-- Theorem 1. The inversion term of an admissible model inverts closed denotations,
recovers substituted normal forms up to α-equivalence, and reflects semantic validity
of equations to βη-convertibility. -/
theorem theorem_1 (M : AdmissibleModel.{u}) :
    (∀ (ρ : Ty) (a : M.Dom ρ),
      M.IsLambdaDefinable ρ a →
      ∃ (t : Term) (ht : HasType t ρ),
        M.IsPeResult ρ a t ∧ IsClosed t ∧ IsLongBetaNormal ρ t ∧
          ∀ η : M.Env, M.eqM ρ (M.eval ht η) a) ∧
    (∀ (ρ : Ty) (r : Term) (ht : HasType r ρ) (θ : Substitution),
      IsWellTypedSubst θ →
      ∃ rStar : Term,
        HasType rStar ρ ∧ IsLongBetaNormal ρ rStar ∧ BetaEtaEq r rStar ∧
        ∃ t : Term,
          M.IsPeResult ρ (M.eval ht (M.etaSubst θ)) t ∧
          AlphaEq t (applySubst θ rStar)) ∧
    (∀ {ρ : Ty} {r s : Term} (hr : HasType r ρ) (hs : HasType s ρ),
      M.ModelsEq hr hs → BetaEtaEq r s) := by
  sorry

end BergerSchwichtenberg1991V2
