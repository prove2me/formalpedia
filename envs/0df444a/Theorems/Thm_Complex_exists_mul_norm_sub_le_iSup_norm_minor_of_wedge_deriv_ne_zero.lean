-- Prove2me | Theorems.Thm_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero
-- name    : Complex.exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/e1051fd9-1ec7-50d5-87b1-8306c480944d
-- title:
--   Minor lower bound near an immersed point of a holomorphic curve
-- statement:
--   Let $r$ be a natural number, $\varphi:\mathbb{C}\to(\mathrm{Fin}\,r\to\mathbb{C})$ a function of a complex variable with $r$ complex coordinates, $c\in\mathbb{C}$ and $R$ a real number with $0<R$. Assume that for every index $i$ the coordinate function $z\mapsto\varphi(z)_i$ is differentiable on the open ball $B(c,R)$ (in the sense of `DifferentiableOn ℂ`), and that for some pair of indices $(p_1,p_2)$ one has
--   $$\varphi(c)_{p_1}\,\bigl(\tfrac{d}{dz}\varphi(z)_{p_2}\bigr)(c)-\varphi(c)_{p_2}\,\bigl(\tfrac{d}{dz}\varphi(z)_{p_1}\bigr)(c)\neq 0,$$
--   the derivatives being Mathlib's `deriv`. The conclusion asserts the existence of real numbers $\rho>0$ and $C>0$ such that for all $z,w\in B(c,\rho)$,
--   $$C\,\lVert z-w\rVert\;\le\;\sup_{(p_1,p_2)\in\mathrm{Fin}\,r\times\mathrm{Fin}\,r}\bigl\lVert \varphi(z)_{p_1}\varphi(w)_{p_2}-\varphi(z)_{p_2}\varphi(w)_{p_1}\bigr\rVert,$$
--   the supremum being over the finite index set of pairs, hence a maximum of the absolute values of the $2\times 2$ minors of the pair of vectors $(\varphi(z),\varphi(w))$. The non-vanishing hypothesis forces $r\ge 1$, so the statement is vacuous for $r=0$.
--
--   This is the lower half of the two-sided comparison $\max_{k,\ell}|\varphi_k(z)\varphi_\ell(w)-\varphi_\ell(z)\varphi_k(w)|\asymp|z-w|$ valid near a point where the associated projective curve $z\mapsto[\varphi(z)]$ is unramified, the hypothesis $\varphi(c)\wedge\varphi'(c)\neq0$ expressing exactly that unramifiedness. It is used in the archimedean estimates for sections on modular curves, via [`ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge`](thm.html#ModularCurve.JZero.exists_hyperplaneSection_sum_log_secVal_ge).
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

theorem Complex.exists_mul_norm_sub_le_iSup_norm_minor_of_wedge_deriv_ne_zero {r : ℕ} {φ : ℂ → Fin r → ℂ} {c : ℂ}
    {R : ℝ} (hR : 0 < R) (hφ : ∀ i, DifferentiableOn ℂ (fun z ↦ φ z i) (Metric.ball c R))
    (hw : ∃ p : Fin r × Fin r,
      φ c p.1 * deriv (fun z ↦ φ z p.2) c - φ c p.2 * deriv (fun z ↦ φ z p.1) c ≠ 0) :
    ∃ ρ > 0, ∃ C > 0, ∀ z ∈ Metric.ball c ρ, ∀ w ∈ Metric.ball c ρ,
      C * ‖z - w‖ ≤ ⨆ p : Fin r × Fin r, ‖φ z p.1 * φ w p.2 - φ z p.2 * φ w p.1‖ := by sorry
