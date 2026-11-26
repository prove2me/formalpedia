-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eq_of_isMaxOn_of_laplacian_nonneg
-- name    : FiniteEnergyPlane.eq_of_isMaxOn_of_laplacian_nonneg
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T17:30:47.12699+00:00
-- url     : https://prove2.me/theorems/14034a60-89f0-52f1-9c32-926e58e4ce62
-- title:
--   Strong maximum principle for subharmonic functions in the plane
-- statement:
--   Let $\Omega \subseteq \mathbb{C}$ be open and connected and let $f : \mathbb{C} \to \mathbb{R}$ be $C^2$ on $\Omega$ with $\Delta f = \partial_s^2 f + \partial_t^2 f \ge 0$ on $\Omega$. If $f(z) \le f(z_0)$ for all $z \in \Omega$, for some $z_0 \in \Omega$, then $f \equiv f(z_0)$ on $\Omega$.
--
--   Role: the planar form, on $\mathbb{C}$ with Mathlib's Laplacian, of the strong maximum principle; it applies directly to functions of a complex variable such as the $\mathbb{R}$-coordinate of a pseudoholomorphic curve.
--
--   Formalization Note: $\Delta$ is Mathlib's `InnerProductSpace.laplacian` for the standard real inner product on $\mathbb{C}$, i.e. $\partial_s^2 f + \partial_t^2 f$ with $z = s + it$. Connected is `IsPreconnected` (the empty set is allowed; the statement is then vacuous).
-- source:
--   L. C. Evans, Partial Differential Equations, 2nd ed., AMS (2010), Section 6.4.2; D. Gilbarg, N. S. Trudinger, Elliptic Partial Differential Equations of Second Order, Springer (2001), Section 3.1

import Mathlib.Analysis.InnerProductSpace.Laplacian
import Mathlib.Analysis.Complex.Basic

namespace FiniteEnergyPlane

open Laplacian

/-- Strong maximum principle in the plane. Let `Ω ⊆ ℂ` be open and connected and let `f : ℂ → ℝ` be
`C²` on `Ω` with nonnegative Laplacian `Δf = ∂ₛ²f + ∂ₜ²f ≥ 0` there. If `f` attains its maximum over
`Ω` at a point `z₀ ∈ Ω`, then `f` is constant on `Ω`. -/
theorem eq_of_isMaxOn_of_laplacian_nonneg {Ω : Set ℂ} {f : ℂ → ℝ} (hΩ : IsOpen Ω)
    (hconn : IsPreconnected Ω) (hf : ContDiffOn ℝ 2 f Ω) (hΔ : ∀ z ∈ Ω, 0 ≤ Δ f z)
    {z₀ : ℂ} (hz₀ : z₀ ∈ Ω) (hmax : ∀ z ∈ Ω, f z ≤ f z₀) :
    ∀ z ∈ Ω, f z = f z₀ := by
  sorry

end FiniteEnergyPlane
