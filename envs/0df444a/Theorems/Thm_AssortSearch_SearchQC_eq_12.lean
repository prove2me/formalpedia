-- Prove2me | Theorems.Thm_AssortSearch_SearchQC_eq_12
-- name    : AssortSearch.SearchQC.eq_12
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:30:24.551525+00:00
-- url     : https://prove2.me/theorems/20385dc0-3af9-4694-a5a6-56dd6185afff
-- title:
--   (12): $2-2e^{-\lambda(v_j+V_S)}-\lambda(v_j+V_S)e^{-\lambda(v_j+V_S)}-\lambda(v_j+V_S)<0$
-- statement:
--   Let $\lambda>0$ and let $v_j,V_S$ be real numbers with $v_j+V_S>0$. Then
--   $$2-2\exp[-\lambda(v_j+V_S)]-\lambda(v_j+V_S)\exp[-\lambda(v_j+V_S)]-\lambda(v_j+V_S)<0.$$
--
--   In the proof of Theorem 5 this is the inequality to which condition (11) reduces in Case (2), $f(v_j)\ge0$ and $g(v_j)\ge0$; the paper states that it "holds for all $v_j+V_s>0$". Equivalently, with $t=\lambda(v_j+V_S)>0$, $2-2e^{-t}-te^{-t}-t<0$.
-- source:
--   Cachon, Terwiesch & Xu, Retail Assortment Planning in the Presence of Consumer Search, working paper (Dec. 20, 2002), p. 17 (PDF 19), proof of Theorem 5, display (12)

import Mathlib

namespace AssortSearch.SearchQC

/-- (12), p. 17: for `λ > 0` and `v_j + V_S > 0`,
`2 - 2 e^{-λ(v_j+V_S)} - λ(v_j+V_S) e^{-λ(v_j+V_S)} - λ(v_j+V_S) < 0`. -/
theorem eq_12 (lam x VS : ℝ) (hlam : 0 < lam) (hW : 0 < x + VS) :
    2 - 2 * Real.exp (-(lam * (x + VS))) - lam * (x + VS) * Real.exp (-(lam * (x + VS)))
      - lam * (x + VS) < 0 := by sorry

end AssortSearch.SearchQC
