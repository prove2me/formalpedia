-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991V2_lemma_5
-- name    : BergerSchwichtenberg1991V2.lemma_5
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:14:43.804328+00:00
-- url     : https://prove2.me/theorems/ad1182c8-8caf-4797-af99-abb133a9b25c
-- title:
--   Lemma 5 — Reification of substituted long normal forms
-- statement:
--   For a well-typed long $\beta$-normal term and a well-typed substitution, quotation of the value in the substitution environment is the family of the substituted term. At ground type the value itself is the code of the representative selected by extraction.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg (1991), An inverse of the evaluation functional for typed lambda-calculus, LICS, pp. 203–211, Lemma 5, p. 207. https://epub.ub.uni-muenchen.de/4261/1/4261.pdf

import Definitions.Def_BergerSchwichtenberg1991V2_Models

namespace BergerSchwichtenberg1991V2

universe u

/-- Lemma 5. Evaluating a long normal term in the environment induced by a typed
substitution and quoting the result gives the family of the substituted term.
At ground type its value is the code of the representative selected by extraction. -/
theorem lemma_5 (M : AdmissibleModel.{u}) {ρ : Ty} {r : Term} (θ : Substitution)
    (ht : HasType r ρ) (hnorm : IsLongBetaNormal ρ r) (hθ : IsWellTypedSubst θ) :
    M.eqM M.tyF
      (M.appM (M.phi ρ) (M.eval ht (M.etaSubst θ)))
      (M.appM M.emb (M.codeTerm (applySubst θ r))) ∧
    (∀ hbase : ρ = .base,
      M.eqM .base
        (hbase ▸ M.eval ht (M.etaSubst θ))
        (M.codeTerm (EXTRACT (EMB (applySubst θ r))))) := by
  sorry

end BergerSchwichtenberg1991V2
