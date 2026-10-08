-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_theorem_3_4_subdiff_to_prox
-- name    : ErrBoundQG.ProxGrad.theorem_3_4_subdiff_to_prox
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:09.809044+00:00
-- url     : https://prove2.me/theorems/681dfa0b-5805-448e-adfe-c7a0907c7de9
-- title:
--   Theorem 3.4, (3.8) ⇒ (3.9), p. 7 — the subdifferential error bound gives the proximal error bound with L̂ = L + t
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ be a proper closed convex function with nonempty set of minimizers $S$ and minimal value $h^*$, and let $\nu>0$, $L>0$ and $t>0$. Suppose
--   $$\operatorname{dist}(x;S)\ \le\ L\cdot\operatorname{dist}\big(0;\partial h(x)\big)\qquad\text{for all } x\in[h\le h^*+\nu].$$
--   Then, with $\widehat L = L + t$,
--   $$\operatorname{dist}(x;S)\ \le\ \widehat L\cdot t^{-1}\big\|x - \operatorname{prox}_{th}(x)\big\|\qquad\text{for all } x\in[h\le h^*+\nu],$$
--   where $\operatorname{prox}_{th}(x) = \operatorname{argmin}_y\{h(y)+\frac1{2t}\|y-x\|^2\}$.
--
--   This turns the subdifferential error bound into the corresponding bound for the proximal point map; with $h=\varphi$ it is the middle step of the proof of Corollary 3.6.
--
--   **Formalization Note** $\operatorname{prox}_{th}(x)$ is any $p$ satisfying `IsProxPoint (fun y => t * h y) x p` ($p$ minimizes $t\,h(y)+\frac12\|y-x\|^2$); the conclusion is stated for every such $p$, which is faithful since the minimizer exists and is unique. The hypothesis on $\operatorname{dist}(0;\partial h(x))$ is encoded as "for every $v\in\partial h(x)$, $\operatorname{dist}(x;S)\le L\|v\|$".
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 7, Theorem 3.4, (3.8) ⇒ (3.9)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxGrad_Setting

namespace ErrBoundQG.ProxGrad

theorem theorem_3_4_subdiff_to_prox {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (hh : RockafellarMaxMono.Shared.ProperConvex h) (hhc : LowerSemicontinuous h)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S = minSet h) (hSne : S.Nonempty)
    (hstar : ℝ) (hhstar : ∀ x ∈ S, h x = (hstar : EReal)) (ν : ℝ) (hν : 0 < ν)
    (L t : ℝ) (hL : 0 < L) (ht : 0 < t) (hEB : SubdiffErrorBound h S hstar L ν) :
    ProxErrorBound h S hstar (L + t) t ν := by sorry

end ErrBoundQG.ProxGrad
