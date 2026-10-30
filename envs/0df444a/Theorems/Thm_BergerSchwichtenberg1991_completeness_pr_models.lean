-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991_completeness_pr_models
-- name    : BergerSchwichtenberg1991.completeness_pr_models
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T02:08:44.442009+00:00
-- url     : https://prove2.me/theorems/c4cdb23c-1935-4e0d-9eaa-5d27cd2e4606
-- title:
--   Inversion, Normalization, and Strong Completeness Theorem for pr-Models
-- statement:
--   In any `pr-model` `M`, there is a λ-definable functional `inv_ρ : M^ρ → M^o` computing the Gödel number of the long β-normal form of any closed λ-term denoting `a ∈ M^ρ`, and `M ⊨ r = s` implies `r =_{βη} s` (Section 4, p. 208).
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Inversion and Normalization Theorem & Completeness Theorem, p. 208.

import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem completeness_pr_models :
    (∀ (M : PRModel.{u}) (N : EffectiveNumbering)
       (hExtractComb :
         ∀ indextBar : M.Dom (.arr .base (.arr .base .base)),
           ∃ extractBar : M.Dom (.arr (.arr .base .base) .base),
             ∀ a : M.Dom (.arr .base .base),
               M.eqM .base (M.appM extractBar a)
                 (M.appM a
                   (M.appM
                     (M.appM indextBar (M.appM a (M.nu (N.natOfIdx epsIdx))))
                     (M.appM a (M.nu (N.natOfIdx zeroIdx))))))
       (hStepComb :
         ∀ (abstBar : Ty → M.Dom (.arr .base (.arr .base .base)))
           (funBar appendBar : M.Dom (.arr .base (.arr .base .base)))
           (ρ : Ty) (body : M.Dom .base → M.Dom .base),
           (∀ p₁ p₂ : M.Dom .base, M.eqM .base p₁ p₂ → M.eqM .base (body p₁) (body p₂)) →
           ∃ step : M.Dom (.arr .base .base),
             ∀ p : M.Dom .base,
               M.eqM .base (M.appM step p)
                 (M.appM (M.appM (abstBar ρ) p)
                   (M.appM (M.appM funBar (body p))
                     (M.appM (M.appM appendBar p) (M.nu (N.natOfIdx zeroIdx))))))
       (hIF :
         ∀ A : AdmissibleModel.{u},
           A.toLambdaModel = M.toLambdaModel →
           Nonempty (InversionFunctionals A)),
      ∃ (A : AdmissibleModel.{u}) (IF : InversionFunctionals A),
        A.toLambdaModel = M.toLambdaModel ∧
        (∀ t : Term, HEq (A.codeTerm t) (M.nu (N.natOfTerm t))) ∧
        (∀ (ρ : Ty) (a : A.Dom ρ),
          A.IsLambdaDefinable ρ a →
          ∃ r : Term,
            HasType r ρ ∧
            IsClosed r ∧
            IsLongBetaNormal ρ r ∧
            A.eqM .base (IF.invCode ρ a) (A.codeTerm r) ∧
            ∀ η : A.Env, A.eqM ρ (A.eval r η ρ) a) ∧
        (∀ (ρ : Ty) (r s : Term),
          HasType r ρ →
          HasType s ρ →
          M.ModelsEq ρ r s →
          BetaEtaEq r s)) := by sorry

end BergerSchwichtenberg1991
