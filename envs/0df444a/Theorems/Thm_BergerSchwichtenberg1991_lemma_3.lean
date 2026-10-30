-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991_lemma_3
-- name    : BergerSchwichtenberg1991.lemma_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T02:08:05.148707+00:00
-- url     : https://prove2.me/theorems/c9134df5-456e-42b1-8651-6eec851d26bf
-- title:
--   Lemma 3: Every pr-Model is Admissible
-- statement:
--   Every λ-model `M` representing all unary and binary primitive recursive functions (`PRModel`) with an effective repetition-free numbering (`EffectiveNumbering`) and the required λ-combinators can be equipped with an admissible model structure (`AdmissibleModel`) with `f = ι = o`.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Lemma 3, p. 206.

import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem lemma_3 (M : PRModel.{u}) (N : EffectiveNumbering)
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
                  (M.appM (M.appM appendBar p) (M.nu (N.natOfIdx zeroIdx)))))) :
    ∃ A : AdmissibleModel.{u},
      A.toLambdaModel = M.toLambdaModel ∧
      A.tyF = .base ∧
      A.tyIdx = .base ∧
      (∀ r : Term, HEq (A.codeTerm r) (M.nu (N.natOfTerm r))) ∧
      (∀ k : Index, HEq (A.codeIdx k) (M.nu (N.natOfIdx k))) := by sorry

end BergerSchwichtenberg1991
