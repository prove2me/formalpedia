-- Prove2me | Theorems.Thm_BnBPEP_WeakCvx_eq_32_one_step
-- name    : BnBPEP.WeakCvx.eq_32_one_step
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T06:47:09.669995+00:00
-- url     : https://prove2.me/theorems/559efd65-5421-4cdd-bab7-edf88812b4b6
-- title:
--   (32) — one-step potential inequality $\|f'(y_k)\|^2+\psi_{k+1}-\psi_k\le c_k\|f'(x_k)\|^2$
-- statement:
--   Let $L>0$ and $f\in\mathcal W_{1,L}$, and let $x_\star$ be a global minimizer of $f$. Let $h\ge0$ and $b_{k+1}\ge0$ with $h\,b_{k+1}\le2$, and put
--   $$b_k=4+(1-2h)\,b_{k+1},\qquad c_k=h^2 b_{k+1}.$$
--   Take an arbitrary point $x_k\in\mathbb R^d$, an arbitrary subgradient $f'(x_k)\in\partial f(x_k)$, and one step of the subgradient method $x_{k+1}=x_k-h\,f'(x_k)$. Let $y_k=\mathrm{prox}_{(1/2)f}(x_k)$, $y_{k+1}=\mathrm{prox}_{(1/2)f}(x_{k+1})$ (minimizers of $z\mapsto f(z)+\|z-x\|^2$), $f'(y_k)=2(x_k-y_k)$, and
--   $$\psi_j=b_j\big(f(y_j)-f(x_\star)+\|x_j-y_j\|^2\big),\qquad j\in\{k,k+1\}.$$
--   Then
--   $$\|f'(y_k)\|^2+\psi_{k+1}-\psi_k\ \le\ c_k\,\|f'(x_k)\|^2.\tag{32}$$
--
--   The inequality is established one iteration at a time, oblivious to how $x_k$ was generated; summed over $k\in[0:N]$ it telescopes into the rate of Theorem 1.
--
--   **Formalization Note** The parameters $b_k$, $c_k$ are the ones of (43) and Theorem 1, written as $4+(1-2h)b_{k+1}$ and $h^2b_{k+1}$. The hypotheses $b_{k+1}\ge0$, $h\ge0$, $hb_{k+1}\le2$ are exactly the nonnegativity of the four weights $b_{k+1}$, $2hb_{k+1}$, $2hb_{k+1}$, $b_k-b_{k+1}=4-2hb_{k+1}$ of the alternate proof of Theorem 1 (pp. 625–627); under Theorem 1's hypotheses they follow from (44). Subgradients are those of the weak-convexity inequality with modulus $1$; $\|\cdot\|^2$ of $f'(y_k)$ is written $\|2(x_k-y_k)\|^2$.
-- source:
--   Das Gupta, Van Parys, Ryu, Branch-and-bound performance estimation programming, Math. Program. 204 (2024), §6.3.2, p. 616, (32); ψ_k and (31) on p. 615; (43) on p. 622; proved in the alternate proof of Theorem 1, pp. 625–627

import Mathlib
import Definitions.Def_SAGA_Convex_IsProxPoint
import Definitions.Def_BnBPEP_WeakCvx_IsWeakSubgrad
import Definitions.Def_BnBPEP_WeakCvx_InWeakClass

namespace BnBPEP.WeakCvx

/-- (32), p. 616, proved in the alternate proof of Theorem 1, pp. 625–627: one step
`x_{k+1} = x_k - h f'(x_k)` of the subgradient method from an arbitrary point `x_k`, with
`y_k = prox_{(1/2)f}(x_k)`, `y_{k+1} = prox_{(1/2)f}(x_{k+1})`, `f'(y_k) = 2(x_k - y_k)`,
`b_k = 4 + (1 - 2h) b_{k+1}` and `c_k = h² b_{k+1}`, satisfies
`‖f'(y_k)‖² + ψ_{k+1} - ψ_k ≤ c_k ‖f'(x_k)‖²` whenever the weights
`b_{k+1}, 2h b_{k+1}, 4 - 2h b_{k+1}` of the alternate proof are nonnegative. -/
theorem eq_32_one_step {d : ℕ} (f : EuclideanSpace ℝ (Fin d) → ℝ) (L : ℝ)
    (hL : 0 < L) (hf : InWeakClass 1 L f)
    (xstar : EuclideanSpace ℝ (Fin d)) (hxstar : ∀ z, f xstar ≤ f z)
    (h bk1 : ℝ) (hh : 0 ≤ h) (hb : 0 ≤ bk1) (hhb : h * bk1 ≤ 2)
    (xk gk xk1 yk yk1 : EuclideanSpace ℝ (Fin d))
    (hg : IsWeakSubgrad 1 f xk gk) (hstep : xk1 = xk - h • gk)
    (hyk : SAGA.Convex.IsProxPoint f (1 / 2) xk yk)
    (hyk1 : SAGA.Convex.IsProxPoint f (1 / 2) xk1 yk1) :
    ‖(2 : ℝ) • (xk - yk)‖ ^ 2 + bk1 * (f yk1 - f xstar + ‖xk1 - yk1‖ ^ 2)
        - (4 + (1 - 2 * h) * bk1) * (f yk - f xstar + ‖xk - yk‖ ^ 2)
      ≤ h ^ 2 * bk1 * ‖gk‖ ^ 2 := by sorry

end BnBPEP.WeakCvx
