-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_theorem_3_3_qg_to_eb
-- name    : ErrBoundQG.ProxGrad.theorem_3_3_qg_to_eb
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:09.072361+00:00
-- url     : https://prove2.me/theorems/0a0fb091-ab6d-43c7-acf8-3ccbcd1ffb92
-- title:
--   Theorem 3.3, (3.6) ⇒ (3.7), pp. 6–7 — quadratic growth gives the subdifferential error bound with L = 2α⁻¹
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ be a proper closed convex function with nonempty set of minimizers $S$ and minimal value $h^*$, and let $\nu>0$ and $\alpha>0$. Suppose $h$ grows quadratically on the sublevel set $[h\le h^*+\nu]$:
--   $$h(x)\ \ge\ h^* + \frac{\alpha}{2}\operatorname{dist}^2(x;S)\qquad\text{for all } x\in[h\le h^*+\nu].$$
--   Then the subdifferential error bound holds with $L = 2\alpha^{-1}$:
--   $$\operatorname{dist}(x;S)\ \le\ \frac{2}{\alpha}\operatorname{dist}\big(0;\partial h(x)\big)\qquad\text{for all } x\in[h\le h^*+\nu].$$
--
--   This is the first half of Theorem 3.3, which links growth of a convex function away from its minimizers to the size of its subgradients; it is the first step of the proof of Corollary 3.6.
--
--   **Formalization Note** The page writes $h(\bar x)$ in (3.6) with no $\bar x$ in scope; it is the minimal value $h^*$, as in (3.12). The distance $\operatorname{dist}(0;\partial h(x))$ is encoded as "for every $v\in\partial h(x)$, $\operatorname{dist}(x;S)\le\frac2\alpha\|v\|$", so the bound holds trivially where $\partial h(x)=\emptyset$, as on the page.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, pp. 6–7, Theorem 3.3, (3.6) ⇒ (3.7)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxGrad_Setting

namespace ErrBoundQG.ProxGrad

theorem theorem_3_3_qg_to_eb {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (hh : RockafellarMaxMono.Shared.ProperConvex h) (hhc : LowerSemicontinuous h)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S = minSet h) (hSne : S.Nonempty)
    (hstar : ℝ) (hhstar : ∀ x ∈ S, h x = (hstar : EReal)) (ν : ℝ) (hν : 0 < ν)
    (α : ℝ) (hα : 0 < α) (hQG : QuadGrowth h S hstar α ν) :
    SubdiffErrorBound h S hstar (2 * α⁻¹) ν := by sorry

end ErrBoundQG.ProxGrad
