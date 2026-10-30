-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_lemma_3_4
-- name    : AehligSchwichtenberg2002.lemma_3_4
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:56:23.377843+00:00
-- url     : https://prove2.me/theorems/be7ab9df-d8b3-4216-8d1c-e9c3541e5d96
-- title:
--   Lemma 3.4: Linear Substitution Decreases Weight `μ`
-- statement:
--   For any term `r` and linear variable `x` occurring at most once in `r` outside `!`-subterms, `μ(r[s/x]) < μ((λx. r)s)`.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Lemma 3.4, p. 392.

import Definitions.Def_AehligSchwichtenberg2002_Syntax

namespace AehligSchwichtenberg2002

theorem lemma_3_4 {Γ₁ Γ₁' Γ₂ Γ : Context} {x : Var} {t s : Term} {τ : Ty}
    (hu₁ : IsCtxUnion Γ₁ [x] Γ₁')
    (ht : HasType Γ₁' t τ)
    (hs : HasType Γ₂ s x.ty)
    (hdj : IsDisjointCtxUnion Γ₁ Γ₂ Γ) :
    HasType Γ (substTerm t x s) τ := by sorry

end AehligSchwichtenberg2002
