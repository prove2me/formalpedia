-- Prove2me | Theorems.Thm_FiniteEnergyPlane_forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos
-- name    : FiniteEnergyPlane.forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-06T19:28:49.958655+00:00
-- url     : https://prove2.me/theorems/3d4e1d3e-b9e1-4dbc-a027-b571e6daadeb
-- title:
--   A generalized analytic function of nonpositive winding at infinity vanishes identically or nowhere
-- statement:
--   Let $\zeta:\mathbb C\to\mathbb C$ be smooth and suppose that near every point there is a constant $M$ with $|\partial_s\zeta+i\partial_t\zeta|\le M|\zeta|$. If $\zeta$ has no zeros on $\{|z|\ge R\}$ and its winding number along the counterclockwise circle of radius $R$ is at most $0$, then either $\zeta\equiv 0$ or $\zeta$ has no zeros at all.
--
--   This is a zero-counting statement for generalized analytic functions on the plane, usable whenever the winding at infinity of such a function is known.
--
--   Formalization Note: $\partial_s\zeta$ and $\partial_t\zeta$ are `fderiv ℝ ζ z 1` and `fderiv ℝ ζ z Complex.I`; the circle is `ccwLoop R`; `HasLoopWind` is the winding number of a continuous $1$-periodic loop in $\mathbb C\setminus\{0\}$.
-- source:
--   Zero counting for generalized analytic functions (similarity principle), as used in Hofer-Wysocki-Zehnder, The dynamics on three-dimensional strictly convex energy surfaces (1998)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Let `ζ : ℂ → ℂ` be smooth with `|∂ₛζ + i ∂ₜζ| ≤ M |ζ|` locally, without zeros on `‖z‖ ≥ R`, and
with winding number `k ≤ 0` along the counterclockwise circle of radius `R`. Then `ζ` vanishes
identically or has no zeros. -/
theorem forall_eq_zero_or_forall_ne_zero_of_hasLoopWind_nonpos (ζ : ℂ → ℂ)
    (hζ : ContDiff ℝ ∞ ζ)
    (hM : ∀ z₀ : ℂ, ∃ ρ > (0 : ℝ), ∃ M : ℝ, ∀ z ∈ ball z₀ ρ,
      ‖fderiv ℝ ζ z 1 + Complex.I * fderiv ℝ ζ z Complex.I‖ ≤ M * ‖ζ z‖)
    (R : ℝ) (hR : 0 < R) (hnon : ∀ z, R ≤ ‖z‖ → ζ z ≠ 0) (k : ℤ) (hk0 : k ≤ 0)
    (hk : HasLoopWind (fun t => ζ (ccwLoop R t)) k) :
    (∀ z, ζ z = 0) ∨ ∀ z, ζ z ≠ 0 := by
  sorry

end FiniteEnergyPlane
