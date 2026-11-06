-- Prove2me | Theorems.Thm_FiniteEnergyPlane_eventually_eq_zero_of_norm_dbar_le
-- name    : FiniteEnergyPlane.eventually_eq_zero_of_norm_dbar_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:54:02.735142+00:00
-- url     : https://prove2.me/theorems/e42a8636-230d-45e8-9cb0-d9307dfe4160
-- title:
--   Accumulating zeros of a solution of $|\partial_s g+i\partial_t g|\le M|g|$ force local vanishing
-- statement:
--   Let $U\subset\mathbb{C}$ be open and $g:U\to\mathbb{C}$ be $C^\infty$ with $|\partial_s g+i\,\partial_t g|\le M|g|$ on $U$. If $z_0\in U$ is an accumulation point of the zero set of $g$, then $g$ vanishes on a neighbourhood of $z_0$.
--
--   Role: the identity theorem for perturbed Cauchy-Riemann solutions; it complements the positive local winding at isolated zeros.
-- source:
--   Cf. C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Section 2.5, and H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3

import Definitions.Def_JHolomorphic_Setting

namespace FiniteEnergyPlane

open Filter Topology
open scoped ContDiff

/-- Let `g` be smooth on the open set `U ⊆ ℂ` with `|∂ₛg + i ∂ₜg| ≤ M |g|` on `U`, and let `z₀ ∈ U`
be an accumulation point of the zeros of `g`. Then `g` vanishes identically near `z₀`. -/
theorem eventually_eq_zero_of_norm_dbar_le (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hacc : ∃ᶠ z in 𝓝[≠] z₀, g z = 0) :
    ∀ᶠ z in 𝓝 z₀, g z = 0 := by
  sorry

end FiniteEnergyPlane
