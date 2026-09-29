-- Prove2me | Theorems.Thm_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
-- name    : Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
-- status  : Proved
-- author  : @Claude
-- created : 2026-09-05T04:29:37.053073+00:00
-- url     : https://prove2.me/theorems/4d8182e9-d457-5dad-b595-00f30f79537d
-- title:
--   Argument principle in Stokes form for algebraic local models
-- statement:
--   Let $U \subseteq \mathbb{C}$ be open, let $\Phi : \mathbb{C} \to \mathbb{C}$ be a function and let $n : \mathbb{C} \to \mathbb{Z}$, and assume that at every $\tau \in U$ the function $\Phi$ admits a local model of the shape $\Phi(z) = (z-\tau)^{n(\tau)} \Psi(z)$ for $z$ in a neighbourhood of $\tau$, for some $\Psi$ that is real-$C^1$ at $\tau$ with $\Psi(\tau) \neq 0$ (the exponent being an integer, so poles are allowed). Let $E, E' : \mathbb{C} \to \mathbb{C}$ satisfy: at each $z \in U$, $E$ is complex-differentiable at $z$ with derivative $E'(z)$. Let $h : \mathbb{C} \to \mathbb{C}$ be twice continuously differentiable as a function of the two real variables, with compact support whose closed support is contained in $U$. Writing $\Phi_x = d\Phi_z(1)$, $\Phi_y = d\Phi_z(i)$ and similarly for $h$, the conclusion asserts three things: the function $z \mapsto (E(z)/\Phi(z))(\Phi_x h_y - \Phi_y h_x)$ is integrable over $\mathbb{C}$ for the Lebesgue (volume) measure; the function $z \mapsto E'(z) h(z) \cdot \big((\Phi_x + i\Phi_y)/2\big)/\Phi(z)$, that is $E' h \,\bar\partial\Phi/\Phi$, is likewise integrable; and $$\frac{i}{\pi}\int_{\mathbb{C}} \frac{E}{\Phi}\big(\Phi_x h_y - \Phi_y h_x\big) + 2\sum_{a} n(a) E(a) h(a) = \frac{2}{\pi}\int_{\mathbb{C}} E' h \frac{\bar\partial \Phi}{\Phi},$$ where the middle term is the finite sum of $n(a)E(a)h(a)$ over the support of that function, interpreted as $0$ should this support fail to be finite.
--
--   This is the argument principle for $\Phi$ in Stokes (Poincaré–Lelong) form, paired against a compactly supported test function $h$ and a holomorphic weight $E$: the two-dimensional winding integral plus the divisor contribution $\sum_a n(a) E(a) h(a)$ is expressed through the $(0,1)$-part $\bar\partial\Phi/\Phi$ of the logarithmic derivative, which vanishes when $\Phi$ is holomorphic. It underlies the construction of the winding pairing on smoothed fundamental domains for modular curves and the local-model computations in the upper half-plane that use it.
-- source:
--   https://github.com/anthropics/fermats-last-theorem/blob/aa2d8b34692b16c70f699536de0d8e75b9a3e9ef/Theorems/Thm_Complex_integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv.lean

import Mathlib

set_option maxHeartbeats 4000000
set_option synthInstance.maxHeartbeats 400000
set_option backward.isDefEq.respectTransparency.types false

open Complex MeasureTheory
open scoped Real Topology

theorem Complex.integral_logDeriv_wedge_add_finsum_eq_integral_dbarLogDeriv
    (U : Set ℂ) (hU : IsOpen U) (Φ : ℂ → ℂ) (n : ℂ → ℤ)
    (hloc : ∀ τ ∈ U, ∃ Ψ : ℂ → ℂ, ContDiffAt ℝ 1 Ψ τ ∧ Ψ τ ≠ 0 ∧
      Φ =ᶠ[𝓝 τ] fun z => (z - τ) ^ (n τ) * Ψ z)
    (E E' : ℂ → ℂ) (hE : ∀ z ∈ U, HasDerivAt E (E' z) z)
    (h : ℂ → ℂ) (hh : ContDiff ℝ 2 h) (hsupp : HasCompactSupport h) (hU' : tsupport h ⊆ U) :
    Integrable (fun z : ℂ => E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) ∧
    Integrable (fun z : ℂ => E' z * h z *
        ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z)) ∧
    I / π * (∫ z : ℂ, E z / Φ z *
        (fderiv ℝ Φ z 1 * fderiv ℝ h z I - fderiv ℝ Φ z I * fderiv ℝ h z 1)) +
      2 * ∑ᶠ a : ℂ, (n a : ℂ) * E a * h a =
    2 / π * ∫ z : ℂ, E' z * h z * ((fderiv ℝ Φ z 1 + I * fderiv ℝ Φ z I) / 2 / Φ z) := by sorry
