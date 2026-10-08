-- Prove2me | Theorems.Thm_ErrBoundQG_ProxGrad_theorem_3_5_i
-- name    : ErrBoundQG.ProxGrad.theorem_3_5_i
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-07T23:11:05.286989+00:00
-- url     : https://prove2.me/theorems/9cca3dfb-854b-4c83-81cd-028d647f6f0c
-- title:
--   Theorem 3.5, (3.10), p. 8 — the forward-backward step is no longer than dist(0; Φ(x))
-- statement:
--   Let $G,\Phi:\mathbb R^n\rightrightarrows\mathbb R^n$ be maximal monotone operators whose difference $F := \Phi - G$ is single-valued, that is, $\Phi(x) = F(x) + G(x)$ for every $x$ with $F:\mathbb R^n\to\mathbb R^n$. Let $t>0$, let $\operatorname{prox}_{tG} = (I + tG)^{-1}$ be the resolvent of $G$, and let
--   $$\mathcal G_t(x) := \frac1t\Big(x - \operatorname{prox}_{tG}\big(x - tF(x)\big)\Big)$$
--   be the prox-gradient (forward-backward) mapping. Then for every $x\in\mathbb R^n$,
--   $$\|\mathcal G_t(x)\|\ \le\ \operatorname{dist}\big(0;\Phi(x)\big).$$
--
--   With $F=\nabla f$, $G=\partial g$ and $\Phi=\partial\varphi$, this bounds the proximal gradient step by the minimal-norm subgradient of $\varphi = f+g$; it gives the converse direction of Corollary 3.6.
--
--   **Formalization Note** The resolvent is a map $J_G$ with $t^{-1}(x - J_G(x))\in G(J_G(x))$ for every $x$ (the published `IsResolvent t G JG`); for maximal monotone $G$ such a map exists and is unique. "The difference $\Phi - G$ is single-valued" is read as $\Phi(x) = F(x) + G(x)$ (a translate of the set $G(x)$) for a map $F$. The inequality $\le\operatorname{dist}(0;\Phi(x))$ is stated as $\|\mathcal G_t(x)\|\le\|v\|$ for every $v\in\Phi(x)$, which keeps $\operatorname{dist}(0;\emptyset)=+\infty$. The hypothesis that $\Phi$ is maximal monotone is kept, as on the page, although (3.10) does not use it.
-- source:
--   Drusvyatskiy & Lewis, Error bounds, quadratic growth, and linear convergence of proximal methods, arXiv:1602.06661v2, pp. 7–8, Theorem 3.5, (3.10)

import Mathlib
import Definitions.Def_ThreeOpSplitting_Convergence_MonotoneOperators

namespace ErrBoundQG.ProxGrad

theorem theorem_3_5_i {n : ℕ} (G Φ : EuclideanSpace ℝ (Fin n) → Set (EuclideanSpace ℝ (Fin n)))
    (hG : ThreeOpSplitting.Convergence.IsMaximalMonotone G)
    (hΦ : ThreeOpSplitting.Convergence.IsMaximalMonotone Φ)
    (F : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hF : ∀ x, Φ x = (fun w => F x + w) '' G x)
    (t : ℝ) (ht : 0 < t) (JG : EuclideanSpace ℝ (Fin n) → EuclideanSpace ℝ (Fin n))
    (hJG : ThreeOpSplitting.Convergence.IsResolvent t G JG) :
    ∀ x, ∀ v ∈ Φ x, ‖t⁻¹ • (x - JG (x - t • F x))‖ ≤ ‖v‖ := by sorry

end ErrBoundQG.ProxGrad
