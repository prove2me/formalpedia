-- Prove2me | Theorems.Thm_FiniteEnergyPlane_dlambdaDensity_eq_zero_of_proj_mem_range
-- name    : FiniteEnergyPlane.dlambdaDensity_eq_zero_of_proj_mem_range
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-26T23:52:03.113973+00:00
-- url     : https://prove2.me/theorems/eab20a70-2453-5c24-8e03-bec52f13a6b1
-- title:
--   Maps over a periodic Reeb orbit carry no d-lambda density
-- statement:
--   Let $S = H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level, $P = (x,T)$ a prime periodic Reeb orbit on $S$, $U\subseteq\mathbb{C}$ open, and $u:\mathbb{C}\to\mathbb{R}^4$ a map whose radial projection $w = \mathrm{proj}\circ u$ to $S$ takes values in $x(\mathbb{R})$ at every point of $U$. Then the $d\lambda$-density $\omega_0(\partial_s w, \partial_t w)$ of $u$ vanishes at every point of $U$.
--
--   Role: a curve lying over a periodic orbit, i.e. inside the trivial cylinder $\mathbb{R}\times x(\mathbb{R})$, carries no $d\lambda$-energy. This is used to exclude limits of pseudoholomorphic disks that lie entirely in a trivial cylinder.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations II: Embedding controls and algebraic invariants, Geom. Funct. Anal. 5 (1995), Theorem 4.4 (boundary part); U. Hryniewicz, J. Symplectic Geom. 12 (2014), § 3

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric
open scoped ContDiff

/-- Maps over a periodic orbit carry no `dλ`. Let `P = (x, T)` be a prime periodic Reeb orbit on the strictly
star-shaped level `S`, `U ⊆ ℂ` open, and `u : ℂ → V 1` a map whose projection `proj ∘ u` to `S` takes values in
`x(ℝ)` on `U`. Then the `dλ`-density `ω₀(∂ₛ(proj ∘ u), ∂ₜ(proj ∘ u))` of `u` vanishes at every point of `U`. -/
theorem dlambdaDensity_eq_zero_of_proj_mem_range (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (P : ReebOrbit H) (hP : P.IsPrime) (U : Set ℂ) (hU : IsOpen U) (u : ℂ → V 1)
    (hu : ∀ z ∈ U, proj H (u z) ∈ Set.range P.x) :
    ∀ z ∈ U, dlambdaDensity H u z = 0 := by
  sorry

end FiniteEnergyPlane
