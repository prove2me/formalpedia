-- Prove2me | Theorems.Thm_AccelMM_BTMap_corollary_4_2
-- name    : AccelMM.BTMap.corollary_4_2
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-21T00:33:57.017991+00:00
-- url     : https://prove2.me/theorems/23308630-3a00-4064-97d8-173df86bcaac
-- title:
--   Corollary 4.2, p. 13 — one rescaled MM step contracts the MAP gap ρ(w*) − ρ(w) by 1 − α_{M,ω,β}
-- statement:
--   Consider the Bradley–Terry model of paired comparisons for $n$ items with comparison counts $d_{i,j}$, co-occurrence matrix $M$, $d(M)=\|M\|_\infty$ and $a(M)=\lambda_2(L_M)$, and the product-form prior $e^{w_i}\sim\mathrm{Gamma}(\alpha,\beta)$ with $\alpha>1$, $\beta>0$. Let $\omega\ge0$ and $W_\omega=\{w:\|w\|_\infty\le\omega\}$, and let $\rho$ be the log-a posteriori function (2.4), $\rho(x;y)$ its MM surrogate and $\Pi$ the rescaling (4.4).
--
--   Let $w^*\in W_\omega$ be a maximizer of $\rho$ (the MAP estimate). Let $w=w^{(t)}\in W_\omega$ be an iterate of the $\Pi$-transformed MM algorithm, i.e. $w=\Pi(v)$ for some $v$, such that the virtual gradient point
--   $$w+\frac{1}{\mu+\delta}\nabla\rho(w),\qquad \mu=\frac{d(M)}2+e^{\omega}\beta,\quad\delta=\frac{e^{2\omega}d(M)}{2},$$
--   lies in $W_\omega$. Let $x'$ be any maximizer of $\rho(\cdot\,;w)$, so that $w^{(t+1)}=\Pi(x')$. Then
--   $$\rho(w^*)-\rho(w^{(t+1)})\le(1-\alpha_{M,\omega,\beta})\bigl(\rho(w^*)-\rho(w^{(t)})\bigr),\qquad \alpha_{M,\omega,\beta}=\frac{2c_\omega a(M)+2e^{-\omega}\beta}{(1+e^{2\omega})d(M)+2e^{\omega}\beta},$$
--   where $c_\omega=1/(e^{-\omega}+e^{\omega})^2$.
--
--   The rate depends on the algebraic connectivity $a(M)$ of the comparison graph; for the classic MM algorithm without rescaling (Corollary 3.4) only the prior strength $\beta$ appears, which makes it arbitrarily slow as $\beta\to0$.
--
--   **Formalization Note** Hypotheses restored from the paper's setting: $\alpha>1$ instead of the printed $\alpha\ge1$ ($\Pi$ takes $\log\frac{(\alpha-1)n}{\beta}$); $w^*$ a maximizer of $\rho$ in $W_\omega$ (as in Corollaries 3.3–3.4); $w^{(t)}\in W_\omega$ and $w^{(t)}=\Pi(v)$ (an iterate after at least one rescaling, so that $\nabla\rho(w^{(t)})^\top\mathbf 1=0$ by (4.7)); and the virtual-point condition of Theorem 3.2, needed because smoothness and the surrogate bound hold only on $W_\omega$. The page's "(4.1)" refers to the MM iteration (4.2). The MM step is any maximizer of the surrogate, the paper's argmax.
-- source:
--   Vojnović, Yun & Zhou, Accelerated MM Algorithms for Ranking Scores Inference from Comparison Data, arXiv:1901.00150v3 (26 Dec 2020), p. 13, Corollary 4.2

import Mathlib
import Definitions.Def_AccelMM_BTMap_Framework
import Definitions.Def_AccelMM_BTMap_Model

namespace AccelMM.BTMap

theorem corollary_4_2 {n : ℕ} (d : Fin n → Fin n → ℕ) (α β ω : ℝ)
    (hα : 1 < α) (hβ : 0 < β) (hω : 0 ≤ ω)
    (wstar : E n) (hstar : ∀ w, rho α β d w ≤ rho α β d wstar) (hstarW : wstar ∈ box ω)
    (w : E n) (hwW : w ∈ box ω) (hwPi : ∃ v, w = Pi α β v)
    (hvirt : w + (1 / ((degM d / 2 + Real.exp ω * β) + Real.exp (2 * ω) * degM d / 2)) •
        gradient (rho α β d) w ∈ box ω)
    (xm : E n) (hxm : ∀ z, rhoSurr α β d z w ≤ rhoSurr α β d xm w) :
    rho α β d wstar - rho α β d (Pi α β xm) ≤
      (1 - (2 * cOmega ω * algConn d + 2 * Real.exp (-ω) * β) /
            ((1 + Real.exp (2 * ω)) * degM d + 2 * Real.exp ω * β)) *
        (rho α β d wstar - rho α β d w) := by sorry

end AccelMM.BTMap
