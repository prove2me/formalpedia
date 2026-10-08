-- Prove2me | Theorems.Thm_AssortSearch_SearchQC_eq_8_corrected
-- name    : AssortSearch.SearchQC.eq_8_corrected
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:32:00.655807+00:00
-- url     : https://prove2.me/theorems/344ec2cd-24e9-4246-b2bb-5d82b573a71b
-- title:
--   (8), corrected: $h^{si\prime}(v_j)=\frac{e^{-\lambda(v_j+V_S)}}{(v_j+V_S)^2}[V_S D(v_j)f(v_j)-K(v_j)g(v_j)]$
-- statement:
--   In the setting of (7) (preferences $v_i>0$, $v_0>0$, $\lambda>0$, common margin $m$, cost $c$ differentiable on $(0,1)$, $j\notin S$, $V_S=v_0+\sum_{i\in S}v_i$), for every $v_j>0$,
--   $$h^{si\prime}(v_j)=\frac{e^{-\lambda(v_j+V_S)}}{(v_j+V_S)^2}\Bigl[V_S\,D(v_j)f(v_j)-K(v_j)g(v_j)\Bigr],$$
--   where
--   $$D(v_j)=e^{\lambda(v_j+V_S)}-1+\frac{\lambda v_j}{V_S}(v_j+V_S),\qquad K(v_j)=e^{\lambda(v_j+V_S)}-1-\lambda(v_j+V_S).$$
--
--   This rewriting of (7) factors out the positive term $e^{-\lambda(v_j+V_S)}/(v_j+V_S)^2$, so the sign of $h^{si\prime}$ is that of $V_S Df-Kg$.
--
--   **Formalization Note** The paper's display (8) prints $D(v_j)f(v_j)-K(v_j)g(v_j)$ in the bracket, without the factor $V_S$. From the definitions of $J$ and $N$ one has $J=e^{-\lambda W}V_S D/W^2$ and $N=-e^{-\lambda W}K/W^2$ with $W=v_j+V_S$, so the bracket must be $V_S D f-K g$; the display as printed is false whenever $V_S\ne1$ and $f\ne0$. This item states the corrected identity. The correction does not affect the sign arguments that follow, since $V_S>0$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 15 (PDF 17), proof of Theorem 5, display (8) (corrected: factor V_S restored)

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_Model
import Definitions.Def_AssortSearch_SearchQC_ProofTerms

namespace AssortSearch.SearchQC

/-- (8), p. 15, with the factor `V_S` the printed display omits: for `v_j = x > 0`,
`h^si'(x) = e^{-λ(x+V_S)} / (x+V_S)^2 · [V_S D(x) f(x) - K(x) g(x)]`. -/
theorem eq_8_corrected {n : ℕ} (v : Fin n → ℝ) (v0 lam m : ℝ) (c : ℝ → ℝ)
    (S : Finset (Fin n)) (j : Fin n)
    (hv : ∀ i, 0 < v i) (hv0 : 0 < v0) (hlam : 0 < lam) (hj : j ∉ S)
    (hdiff : DifferentiableOn ℝ c (Set.Ioo 0 1)) (x : ℝ) (hx : 0 < x) :
    HasDerivAt (hSI m c lam v v0 S j)
      (Real.exp (-(lam * (x + VS v v0 S))) / (x + VS v v0 S) ^ 2
        * (VS v v0 S * Dfn lam (VS v v0 S) x * fFn m c lam (VS v v0 S) x
          - Kfn lam (VS v v0 S) x * gFn m c lam v S (VS v v0 S) x)) x := by sorry

end AssortSearch.SearchQC
