-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991_lemma_4
-- name    : BergerSchwichtenberg1991.lemma_4
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T02:08:13.719646+00:00
-- url     : https://prove2.me/theorems/82d84dac-69b9-4561-9992-cfd317faff5f
-- title:
--   Lemma 4: Code-Level Properties of `f-extract`, `f-app`, and `fam`
-- statement:
--   Establishes the four code-level equations (1)-(4) for `f_extract`, `f_app`, and `fam` in any admissible model `M` (Lemma 4, p. 206).
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Lemma 4, p. 206.

import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

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

end BergerSchwichtenberg1991
