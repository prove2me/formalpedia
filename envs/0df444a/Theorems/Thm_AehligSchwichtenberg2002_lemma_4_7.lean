-- Prove2me | Theorems.Thm_AehligSchwichtenberg2002_lemma_4_7
-- name    : AehligSchwichtenberg2002.lemma_4_7
-- status  : Open
-- author  : @kmehltretter82
-- created : 2026-10-30T01:57:19.994125+00:00
-- url     : https://prove2.me/theorems/1fdf124e-5735-4b71-ab33-4fe415758c90
-- title:
--   Lemma 4.7: Exponential Tower Step Bound by Iteration Depth
-- statement:
--   Every term `r` of iteration depth `d = d(r)` normalizes in at most `|r|_d^{2^{d+1}}` reduction steps, with every intermediate term having size at most `|r|_d^{2^d}`.
-- source:
--   Klaus Aehlig and Helmut Schwichtenberg, 'A syntactical analysis of non-size-increasing polynomial time computation', ACM Transactions on Computational Logic 3(3), 2002, pp. 383-401 (LICS 2000, pp. 84-91; doi:10.1145/507382.507386). Lemma 4.7, pp. 396-398.

import Definitions.Def_AehligSchwichtenberg2002_Bounds

namespace AehligSchwichtenberg2002

theorem lemma_4_7 {Γ₁ Γ₂ : Context} {t s : Term} {τ ρ : Ty} (x : Var)
    (ht : HasType Γ₁ t τ)
    (hs : HasType Γ₂ s ρ)
    (hdj : DisjointCtx Γ₁ Γ₂) :
    PolyLe (theta (substTerm t x s)) (fun m => theta t m + theta s m) := by sorry

end AehligSchwichtenberg2002
