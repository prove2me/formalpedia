-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_theorem_3_4_prox_to_subdiff
-- name    : ErrBoundQG.ProxGrad.theorem_3_4_prox_to_subdiff
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:12:19.07796+00:00
-- url     : https://prove2.me/theorems/26d8760e-9405-45d3-b484-656ba47e5210
-- title:
--   Theorem 3.4, (3.9) ⇒ (3.8), p. 7 — the proximal error bound gives the subdifferential error bound with L = L̂
-- statement:
--   Let $h:\mathbb R^n\to\overline{\mathbb R}$ be a proper closed convex function with nonempty set of minimizers $S$ and minimal value $h^*$, and let $\nu>0$, $\widehat L>0$ and $t>0$. Suppose
--   $$\operatorname{dist}(x;S)\ \le\ \widehat L\cdot t^{-1}\big\|x - \operatorname{prox}_{th}(x)\big\|\qquad\text{for all } x\in[h\le h^*+\nu].$$
--   Then
--   $$\operatorname{dist}(x;S)\ \le\ \widehat L\cdot\operatorname{dist}\big(0;\partial h(x)\big)\qquad\text{for all } x\in[h\le h^*+\nu].$$
--
--   This is the converse half of Theorem 3.4: the proximal and the subdifferential error bounds are equivalent up to the constant $t$.
--
--   **Formalization Note** The hypothesis is stated for every $p$ with `IsProxPoint (fun y => t * h y) x p` (the unique proximal point). The conclusion "$\le\widehat L\operatorname{dist}(0;\partial h(x))$" is encoded as "for every $v\in\partial h(x)$, $\operatorname{dist}(x;S)\le\widehat L\|v\|$".
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, p. 7, Theorem 3.4, (3.9) ⇒ (3.8)

import Mathlib
import Definitions.Def_ErrBoundQG_ProxGrad_Setting

namespace ErrBoundQG.ProxGrad

theorem theorem_3_4_prox_to_subdiff {n : ℕ} (h : EuclideanSpace ℝ (Fin n) → EReal)
    (hh : RockafellarMaxMono.Shared.ProperConvex h) (hhc : LowerSemicontinuous h)
    (S : Set (EuclideanSpace ℝ (Fin n))) (hS : S = minSet h) (hSne : S.Nonempty)
    (hstar : ℝ) (hhstar : ∀ x ∈ S, h x = (hstar : EReal)) (ν : ℝ) (hν : 0 < ν)
    (Lhat t : ℝ) (hLhat : 0 < Lhat) (ht : 0 < t) (hPEB : ProxErrorBound h S hstar Lhat t ν) :
    SubdiffErrorBound h S hstar Lhat ν := by sorry

end ErrBoundQG.ProxGrad
