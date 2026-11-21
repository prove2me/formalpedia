-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991V2_completeness_pr_models
-- name    : BergerSchwichtenberg1991V2.completeness_pr_models
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:15:07.273328+00:00
-- url     : https://prove2.me/theorems/24a2ae73-d63b-4c44-9f70-32ca57592cf2
-- title:
--   Canonical-code inversion and strong completeness for pr-models
-- statement:
--   One effective numbering provides canonical codes for all pr-models. In each such model and at every type, there exists an element whose application to any lambda-definable value returns the code of a closed long $\beta$-normal form denoting that value. If terms of the same type agree in every environment of a pr-model, they are $\beta\eta$-convertible.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Section 4, p. 208. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Models

namespace BergerSchwichtenberg1991V2

universe u

/-- The inversion and completeness theorems for pr-models (p. 208). One fixed
effective numbering provides the canonical term codes in every model. At each type
the model contains an inverse on λ-definable elements. Equality in every environment
of a pr-model implies βη-convertibility for terms of the same type. -/
theorem completeness_pr_models :
    (∃ N : EffectiveNumbering,
      ∀ (M : PRModel.{u}) (ρ : Ty),
        ∃ inv : M.Dom (.arr ρ .base),
          ∀ a : M.Dom ρ, M.IsLambdaDefinable ρ a →
            ∃ (t : Term) (ht : HasType t ρ),
              IsClosed t ∧ IsLongBetaNormal ρ t ∧
              M.eqM .base (M.appM inv a) (M.nu (N.natOfTerm t)) ∧
              ∀ η : M.Env, M.eqM ρ (M.eval ht η) a) ∧
    (∀ (M : PRModel.{u}) {ρ : Ty} {r s : Term} (hr : HasType r ρ) (hs : HasType s ρ),
      M.ModelsEq hr hs → BetaEtaEq r s) := by
  sorry

end BergerSchwichtenberg1991V2
