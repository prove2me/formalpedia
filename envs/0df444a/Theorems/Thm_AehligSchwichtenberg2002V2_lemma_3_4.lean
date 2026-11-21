-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_lemma_3_4
-- name    : AehligSchwichtenberg2002V2.lemma_3_4
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-20T20:42:55.266034+00:00
-- url     : https://prove2.me/theorems/84b2b8c0-6fed-42d3-b539-cc726aea7f28
-- title:
--   Lemma 3.4 — Typing of substitution
-- statement:
--   If $\Gamma_1\cup\{x^\rho\}$ types $t$ at $\tau$ and $\Gamma_2$ types $s$ at $\rho$, with $\Gamma_1$ disjoint from $\Gamma_2$, then the capture-avoiding substitution $t[s/x^\rho]$ has type $\tau$ in their disjoint union.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Lemma 3.4. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Syntax

namespace AehligSchwichtenberg2002V2

theorem lemma_3_4 {Γ₁ Γ₁' Γ₂ Γ : Context} {x : Var} {t s : Term} {τ : Ty}
    (hu₁ : IsCtxUnion Γ₁ [x] Γ₁')
    (ht : HasType Γ₁' t τ)
    (hs : HasType Γ₂ s x.ty)
    (hdj : IsDisjointCtxUnion Γ₁ Γ₂ Γ) :
    HasType Γ (substTerm t x s) τ := by sorry

end AehligSchwichtenberg2002V2
