-- Prove2me | Theorems.Thm_FiniteEnergyPlane_false_of_tendstoUniformlyOn_of_boundary_zero
-- name    : FiniteEnergyPlane.false_of_tendstoUniformlyOn_of_boundary_zero
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-26T23:52:03.319801+00:00
-- url     : https://prove2.me/theorems/bc129a93-54c1-58a5-9d8b-480fc38a3b26
-- title:
--   Boundary zeros of Cauchy-Riemann type solutions with real boundary values persist under uniform limits
-- statement:
--   Let $z_1$ be a point of the unit circle, $r > 0$, and $D = \{|z|\le 1\}\cap\{|z - z_1| < r\}$. Let $g$ be smooth on $D$ with $|\partial_s g + i\,\partial_t g| \le M|g|$ and $g \ne 0$ at the interior points $\{|z|<1\}\cap\{|z-z_1|<r\}$, with $g$ real on the arc $\{|z| = 1\}\cap\{|z - z_1| < r\}$, and with $g(z_1) = 0$. Then $g$ is not the uniform limit on $D$ of continuous functions $g_n$ that have no zero on $D$ and are real on the arc.
--
--   Role: a boundary zero of a solution of a Cauchy–Riemann type inequality with real boundary values persists under uniform approximation by functions with the same boundary condition. It is the analytic input for showing that limits of pseudoholomorphic disks with boundary on a spanning disk cannot touch the binding orbit at the boundary.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), Theorem 4.4 (boundary part); U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 3

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Boundary zeros are stable under uniform limits. Let `z₁` lie on the unit circle, `r > 0`, and
`D = closedBall 0 1 ∩ ball z₁ r`. Let `g` be smooth on `D` with `|∂ₛg + i ∂ₜg| ≤ M |g|` at the interior points
`ball 0 1 ∩ ball z₁ r`, nonzero there, real on the arc `sphere 0 1 ∩ ball z₁ r`, and with `g z₁ = 0`. Then `g` is
not the uniform limit on `D` of continuous functions `gₙ` that have no zero on `D` and are real on the arc. -/
theorem false_of_tendstoUniformlyOn_of_boundary_zero (g : ℂ → ℂ) (gn : ℕ → ℂ → ℂ) (z₁ : ℂ)
    (hz₁ : z₁ ∈ sphere (0 : ℂ) 1) (r : ℝ) (hr : 0 < r)
    (hg : ContDiffOn ℝ ∞ g (closedBall 0 1 ∩ ball z₁ r)) (M : ℝ)
    (hM : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r,
      ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (hne : ∀ z ∈ ball (0 : ℂ) 1 ∩ ball z₁ r, g z ≠ 0)
    (hreal : ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (g z).im = 0) (hg₁ : g z₁ = 0)
    (hgn : ∀ n, ContinuousOn (gn n) (closedBall 0 1 ∩ ball z₁ r))
    (hgn_ne : ∀ n, ∀ z ∈ closedBall (0 : ℂ) 1 ∩ ball z₁ r, gn n z ≠ 0)
    (hgn_real : ∀ n, ∀ z ∈ sphere (0 : ℂ) 1 ∩ ball z₁ r, (gn n z).im = 0)
    (hconv : TendstoUniformlyOn gn g Filter.atTop (closedBall 0 1 ∩ ball z₁ r)) :
    False := by
  sorry

end FiniteEnergyPlane
