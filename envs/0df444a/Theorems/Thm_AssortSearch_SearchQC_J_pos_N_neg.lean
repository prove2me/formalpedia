-- Prove2me | Theorems.Thm_AssortSearch_SearchQC_J_pos_N_neg
-- name    : AssortSearch.SearchQC.J_pos_N_neg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:31:30.930679+00:00
-- url     : https://prove2.me/theorems/0b2aacc3-25ed-4555-b5c2-6cf57d1a3c8e
-- title:
--   Proof of Theorem 5: $J(v_j)>0$ and $N(v_j)<0$ for $v_j>0$
-- statement:
--   Let $\lambda>0$ and $V_S>0$, and let $\bar H(v_j)=1-e^{-\lambda(v_j+V_S)}$ with derivative $\bar H'(v_j)=\lambda e^{-\lambda(v_j+V_S)}$. For every $v_j>0$,
--   $$J(v_j)=\frac{\bar H(v_j)V_S+\bar H'(v_j)v_j(v_j+V_S)}{(v_j+V_S)^2}>0,\qquad N(v_j)=\frac{\bar H'(v_j)(v_j+V_S)-\bar H(v_j)}{(v_j+V_S)^2}<0.$$
--
--   The paper observes that $J>0$ "because each term is positive" and asserts $N<0$ ("It can be shown that $N(v_j)<0$"). Together with (7), these signs show that at a critical point of $h^{si}$ the terms $f$ and $g$ have the same sign.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 15 (PDF 17), proof of Theorem 5

import Mathlib
import Definitions.Def_AssortSearch_SearchQC_ProofTerms

namespace AssortSearch.SearchQC

/-- p. 15: for `λ > 0`, `V_S > 0` and `v_j = x > 0`, `J(x) > 0` and `N(x) < 0`. -/
theorem J_pos_N_neg (lam VS x : ℝ) (hlam : 0 < lam) (hVS : 0 < VS) (hx : 0 < x) :
    0 < Jfn lam VS x ∧ Nfn lam VS x < 0 := by sorry

end AssortSearch.SearchQC
