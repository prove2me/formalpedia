-- Prove2me | Theorems.Thm_BergerSchwichtenberg1991_lemma_5
-- name    : BergerSchwichtenberg1991.lemma_5
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T02:08:24.305039+00:00
-- url     : https://prove2.me/theorems/9103856f-178c-455c-8cac-ea09d2f58b0e
-- title:
--   Lemma 5 (Main Lemma): Reification of Long β-Normal Forms in `η_θ`
-- statement:
--   For every long β-normal term `r ∈ Λ^ρ` and well-typed substitution `θ`, `Φ_ρ(|r|_{η_θ}) =_f emb(⌈rθ⌉)`, and if `ρ = o` then `|r|_{η_θ} =_o ⌈EXTRACT(EMB(rθ))⌉`.
-- source:
--   Ulrich Berger and Helmut Schwichtenberg, 'An inverse of the evaluation functional for typed λ-calculus', Proceedings of the Sixth Annual IEEE Symposium on Logic in Computer Science (LICS 1991), pp. 203-211 (doi:10.1109/LICS.1991.151645). Lemma 5 (Main Lemma), p. 207.

import Definitions.Def_BergerSchwichtenberg1991_Models

namespace BergerSchwichtenberg1991

universe u

theorem lemma_5 (M : AdmissibleModel.{u}) (IF : InversionFunctionals M)
    {ρ : Ty} {r : Term} (θ : Substitution)
    (ht : HasType r ρ)
    (hnorm : IsLongBetaNormal ρ r)
    (hθ : IsWellTypedSubst θ) :
    M.eqM M.tyF
      (M.appM (IF.Phi ρ) (M.eval r (IF.etaSubst θ) ρ))
      (M.appM M.emb (M.codeTerm (applySubst θ r))) ∧
    (∀ hbase : ρ = .base,
      M.eqM .base
        (hbase ▸ M.eval r (IF.etaSubst θ) ρ)
        (M.codeTerm (EXTRACT (EMB (applySubst θ r))))) := by sorry

end BergerSchwichtenberg1991
