-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_theorem_3_3_eb_to_qg
-- name    : ErrBoundQG.ProxGrad.theorem_3_3_eb_to_qg
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:08.319222+00:00
-- url     : https://prove2.me/theorems/ce3ae22f-896d-4300-912f-0895cc1b55d4
-- title:
--   Theorem 3.3, (3.7) ⇒ (3.6), p. 7 — the subdifferential error bound gives quadratic growth with any α ∈ (0, 1/L]
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ be a proper closed convex function with nonempty set of minimizers $S$ and minimal value $h^*$, and let $\nu>0$ and $L>0$. Suppose
--   $$\operatorname{dist}(x;S)\ \le\ L\cdot\operatorname{dist}\big(0;\partial h(x)\big)\qquad\text{for all } x\in[h\le h^*+\nu].$$
--   Then for every $\alpha\in(0,1/L]$,
--   $$h(x)\ \ge\ h^* + \frac{\alpha}{2}\operatorname{dist}^2(x;S)\qquad\text{for all } x\in[h\le h^*+\nu].$$
--
--   This is the converse half of Theorem 3.3; the paper refers to Drusvyatskiy–Ioffe [15, Theorem 4.3] and Drusvyatskiy–Mordukhovich–Nghia [19, Theorem 3.1] for the argument. It is the last step of the converse direction of Corollary 3.6.
--
--   **Formalization Note** The hypothesis on $\operatorname{dist}(0;\partial h(x))$ is encoded as "for every $v\in\partial h(x)$, $\operatorname{dist}(x;S)\le L\|v\|$" (distance to the empty set is $+\infty$). The interval $(0,1/L]$ is half-open, exactly as on the page.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 7, Theorem 3.3, (3.7) ⇒ (3.6)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxGrad_Setting

namespace ErrBoundQG.ProxGrad

theorem theorem_3_3_eb_to_qg {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (hh : RockafellarMaxMono.Shared.ProperConvex h) (hhc : LowerSemicontinuous h)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S = minSet h) (hSne : S.Nonempty)
    (hstar : ℝ) (hhstar : ∀ x ∈ S, h x = (hstar : EReal)) (ν : ℝ) (hν : 0 < ν)
    (L : ℝ) (hL : 0 < L) (hEB : SubdiffErrorBound h S hstar L ν) :
    ∀ α ∈ Set.Ioc 0 L⁻¹, QuadGrowth h S hstar α ν := by sorry

end ErrBoundQG.ProxGrad
