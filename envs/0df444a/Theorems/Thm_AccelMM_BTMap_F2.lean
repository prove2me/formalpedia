-- Prove2me | Theorems.Thm_AccelMM_BTMap_F2
-- name    : AccelMM.BTMap.F2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:34:06.548592+00:00
-- url     : https://prove2.me/theorems/3b94eff4-44d4-40e2-9096-6128f9f3c962
-- title:
--   §4.2, p. 13 — condition (F2): −ρ is (c_ω λ₂(L_M) + e^{−ω}β)-PL on W_ω ∩ {∇ρ⊤1 = 0}
-- statement:
--   Let $\alpha\ge1$, $\beta>0$, $\omega\ge0$, and let $w^*$ be a maximizer of the log-a posteriori function $\rho$ with $w^*\in W_\omega$. Then $f=-\rho$ satisfies the $\gamma$-PL inequality, relative to $w^*$, on
--   $$\mathcal X_0=W_\omega\cap\{w:\nabla f(w)^\top\mathbf 1=0\}\qquad\text{with}\qquad\gamma=c_\omega\lambda_2(L_M)+e^{-\omega}\beta;$$
--   that is, for every $w\in\mathcal X_0$,
--   $$\rho(w^*)-\rho(w)\le\frac{1}{2\gamma}\|\nabla\rho(w)\|^2 .$$
--
--   This is condition (F2) of the framework with $d=\mathbf 1$. Compared with Lemma 3.4, the PL constant now contains the algebraic connectivity $a(M)=\lambda_2(L_M)$ and not only the prior strength $\beta$.
--
--   **Formalization Note** That $w^*$ is the maximum a posteriori estimate and lies in $W_\omega$ is the paper's standing setting ("$\mathcal X$ that contains optimum point $x^*$", p. 11). $\lambda_2(L_M)$ is $0$ by convention for $n<2$.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), pp. 12–13, §4.2, condition (F2)

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem F2 {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hα : 1 ≤ α) (hβ : 0 < β) (hω : 0 ≤ ω)
    (wstar : E n) (hstar : ∀ w, rho α β d w ≤ rho α β d wstar) (hstarW : wstar ∈ box ω) :
    PLOn (fun w => -rho α β d w) (X0 (fun w => -rho α β d w) (box ω) (ones n))
      (cOmega ω * algConn d + Real.exp (-ω) * β) wstar := by sorry

end AccelMM.BTMap
