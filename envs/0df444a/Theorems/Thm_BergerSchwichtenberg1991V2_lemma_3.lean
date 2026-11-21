-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991V2_lemma_3
-- name    : BergerSchwichtenberg1991V2.lemma_3
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:14:19.422913+00:00
-- url     : https://prove2.me/theorems/f233af7c-0c58-4200-9269-beeb7a90b3b0
-- title:
--   Lemma 3 — Admissible expansions of pr-models
-- statement:
--   One fixed effective numbering of terms and indices works for every pr-model. Each has an admissible expansion using its ground type for both coding types and its numeral injection to encode the fixed numbering.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Lemma 3, p. 206. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Models

namespace BergerSchwichtenberg1991V2

universe u

/-- Lemma 3 with the coding used in its proof. There is one fixed effective numbering
for all pr-models. Each pr-model admits the stated expansion with both code types
at the ground type and its numeral injection giving the codes. -/
theorem lemma_3 :
    ∃ N : EffectiveNumbering,
      ∀ M : PRModel.{u},
        ∃ A : AdmissibleModel.{u},
          A.toLambdaModel = M.toLambdaModel ∧
          A.tyF = .base ∧ A.tyIdx = .base ∧
          (∀ r : Term, HEq (A.codeTerm r) (M.nu (N.natOfTerm r))) ∧
          (∀ k : Index, HEq (A.codeIdx k) (M.nu (N.natOfIdx k))) := by
  sorry

end BergerSchwichtenberg1991V2
