-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002V2_lemma_4_7
-- name    : AehligSchwichtenberg2002V2.lemma_4_7
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-11-21T06:57:58.82708+00:00
-- url     : https://prove2.me/theorems/a11993db-5bb2-4e87-8f53-b769806a3d3c
-- title:
--   Lemma 4.7 — Substitution bound for the step measure
-- statement:
--   For two typed terms $t,s$ with disjoint typing contexts and a variable $x$, the bound $\vartheta(t[s/x])$ is at most $\vartheta(t)+\vartheta(s)$ pointwise.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg (2002), A syntactical analysis of non-size-increasing polynomial time computation, Lemma 4.7. https://arxiv.org/abs/cs/0011037

import Definitions.Def_AehligSchwichtenberg2002V2_Bounds

namespace AehligSchwichtenberg2002V2

theorem lemma_4_7 {Γ₁ Γ₂ : Context} {t s : Term} {τ ρ : Ty} (x : Var)
    (ht : HasType Γ₁ t τ)
    (hs : HasType Γ₂ s ρ)
    (hdj : DisjointCtx Γ₁ Γ₂) :
    PolyLe (theta (substTerm t x s)) (fun m => theta t m + theta s m) := by sorry

end AehligSchwichtenberg2002V2
