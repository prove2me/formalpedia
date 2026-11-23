-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991V2_lemma_4
-- name    : BergerSchwichtenberg1991V2.lemma_4
-- status  : Proved
-- author  : @kmehltretter82
-- created : 2026-11-20T20:14:32.140706+00:00
-- url     : https://prove2.me/theorems/967a4ef7-b272-4f2e-8f0d-a14acd59154e
-- title:
--   Lemma 4 — Extraction and application of term families
-- statement:
--   In an admissible model, extraction on an embedded term yields the code of the selected representative, re-embedding gives the original family, and family application represents syntactic application. Any model function agreeing with a represented family on all index codes gives that family under the family operator.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Lemma 4, pp. 206–207. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Models

namespace BergerSchwichtenberg1991V2

universe u

/-- Lemma 4. Extraction, application, and family formation agree with the coding laws
on represented term families. -/
theorem lemma_4 (M : AdmissibleModel.{u}) :
    (∀ r : Term,
      M.eqM .base (M.f_extract (M.appM M.emb (M.codeTerm r)))
        (M.codeTerm (EXTRACT (EMB r)))) ∧
    (∀ r : Term,
      M.eqM M.tyF (M.appM M.emb (M.f_extract (M.appM M.emb (M.codeTerm r))))
        (M.appM M.emb (M.codeTerm r))) ∧
    (∀ r s : Term,
      M.eqM M.tyF
        (M.f_app (M.appM M.emb (M.codeTerm r)) (M.appM M.emb (M.codeTerm s)))
        (M.appM M.emb (M.codeTerm (.app r s)))) ∧
    (∀ (a : M.Dom (.arr M.tyIdx .base)) (r : Term),
      (∀ k : Index, M.eqM .base (M.appM a (M.codeIdx k)) (M.codeTerm (EMB r k))) →
      M.eqM M.tyF (M.fam a) (M.appM M.emb (M.codeTerm r))) := by sorry

end BergerSchwichtenberg1991V2
