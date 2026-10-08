-- Prove2me | Theorems.Thm_AssortSearch_SearchQC_eq_7
-- name    : AssortSearch.SearchQC.eq_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:06.92081+00:00
-- url     : https://prove2.me/theorems/2287e066-939d-402c-8534-01561ea11fb6
-- title:
--   (7): $h^{si\prime}(v_j)=J(v_j)f(v_j)+N(v_j)g(v_j)$
-- statement:
--   Consider the independent-assortment search model with preferences $v_i>0$, no-purchase preference $v_0>0$, search parameter $\lambda>0$, common margin $m\in\mathbb R$ and a cost function $c$ differentiable on $(0,1)$. Fix an assortment $S$ and a variant $j\notin S$, and let $h^{si}(v_j)=\pi_j^{si}(v_j)-L^{si}(v_j)$ be the change in profit from adding $j$ with preference $v_j$. Then for every $v_j>0$, $h^{si}$ is differentiable at $v_j$ and
--   $$h^{si\prime}(v_j)=m\,q_j^{si\prime}(v_j)-c'(q_j^{si}(v_j))\,q_j^{si\prime}(v_j)+\sum_{i\in S}\bigl[m\,q_i^{si\prime}(v_j)-c'(q_i^{si}(v_j))\,q_i^{si\prime}(v_j)\bigr]=J(v_j)f(v_j)+N(v_j)g(v_j),$$
--   with $V_S=v_0+\sum_{i\in S}v_i$ and $J,f,N,g$ the functions of the proof of Theorem 5.
--
--   This display opens the proof of Theorem 5: it separates the derivative into the demand-shift coefficients $J,N$, which depend only on $\lambda$ and $V_S$, and the marginal-profit terms $f,g$, which carry the cost function.
--
--   **Formalization Note** The statement is a `HasDerivAt` claim for the function $x\mapsto h^{si}(x)$ at each $x>0$. Only differentiability of $c$ on $(0,1)$ is assumed (concavity is not needed for this identity); $c'$ is `deriv c`.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), pp. 14-15 (PDF 16-17), proof of Theorem 5, display (7)

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_Model
import Definitions.Def_AssortSearch_SearchQC_ProofTerms

namespace AssortSearch.SearchQC

/-- (7), pp. 14–15: for `v_j = x > 0`, `h^si'(x) = J(x) f(x) + N(x) g(x)`, where `V_S`,
`H̄`, `J`, `f`, `N`, `g` are as on p. 14–15 and `c' = deriv c`. -/
theorem eq_7 {n : ℕ} (v : Fin n → ℝ) (v0 lam m : ℝ) (c : ℝ → ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam) (hj : j ∉ S)
    (hdiff : DifferentiableOn ℝ c (Set.Ioo 0 1)) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (hSI m c lam v v0 S j)
      (Jfn lam (VS v v0 S) x * fFn m c lam (VS v v0 S) x
        + Nfn lam (VS v v0 S) x * gFn m c lam v S (VS v v0 S) x) x := by sorry

end AssortSearch.SearchQC
