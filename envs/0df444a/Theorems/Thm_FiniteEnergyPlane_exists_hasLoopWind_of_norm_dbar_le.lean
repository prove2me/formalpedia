-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_hasLoopWind_of_norm_dbar_le
-- name    : FiniteEnergyPlane.exists_hasLoopWind_of_norm_dbar_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:22:01.460469+00:00
-- url     : https://prove2.me/theorems/0cd1c77c-d905-4dc0-a0ba-b018989f1cc7
-- title:
--   An isolated zero of a solution of $|\partial_s g+i\partial_t g|\le M|g|$ has positive winding
-- statement:
--   Let $U\subset\mathbb{C}$ be open and $g:U\to\mathbb{C}$ be $C^\infty$ with $|\partial_s g+i\,\partial_t g|\le M|g|$ on $U$. Let $z_0\in U$ be the only zero of $g$ in $U$. Then there are an integer $m\ge 1$ and $r>0$ such that for every $\rho\in(0,r)$ the loop $t\mapsto g(z_0+\rho e^{2\pi i t})$ lies in $\mathbb{C}\setminus\{0\}$ and has winding number $m$.
--
--   Role: isolated zeros of perturbed Cauchy-Riemann solutions have a well-defined positive local index.
-- source:
--   Cf. C. Wendl, Lectures on Holomorphic Curves in Symplectic and Contact Geometry, arXiv:1011.1690, Section 2.5, and H. Hofer, K. Wysocki, E. Zehnder, GAFA 5 (1995), Section 3

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Let `g` be smooth on the open set `U ⊆ ℂ` with `|∂ₛg + i ∂ₜg| ≤ M |g|` on `U`, and let `z₀ ∈ U` be
the only zero of `g` in `U`. Then there are `m ≥ 1` and `r > 0` such that `g` has winding number `m`
along every counterclockwise circle `t ↦ z₀ + ρ e^{2πit}`, `0 < ρ < r`. -/
theorem exists_hasLoopWind_of_norm_dbar_le (g : ℂ → ℂ) (U : Set ℂ) (hU : IsOpen U)
    (hg : ContDiffOn ℝ ∞ g U) (M : ℝ)
    (hM : ∀ z ∈ U, ‖fderiv ℝ g z 1 + Complex.I * fderiv ℝ g z Complex.I‖ ≤ M * ‖g z‖)
    (z₀ : ℂ) (hz₀ : z₀ ∈ U) (hg₀ : g z₀ = 0) (hiso : ∀ z ∈ U, g z = 0 → z = z₀) :
    ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
      HasLoopWind (fun t => g (z₀ + ccwLoop ρ t)) m := by
  sorry

end FiniteEnergyPlane
