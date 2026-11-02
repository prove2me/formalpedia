-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_endW_ne_proj_reeb_comp
-- name    : FiniteEnergyPlane.exists_endW_ne_proj_reeb_comp
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-01T09:05:27.595353+00:00
-- url     : https://prove2.me/theorems/e5c752a1-56f8-4e86-8563-672e6a80e793
-- title:
--   An end with nonvanishing dλ-density is not a reparametrized Reeb orbit
-- statement:
--   Let $u$ be a finite-energy $\tilde J$-holomorphic curve on $D\setminus\{0\}$ (strictly star-shaped level $S=H^{-1}(1)$, compatible $J$), and suppose that the density $\omega_0(\partial_sw,\partial_tw)$, $w=\mathrm{proj}\circ u$, does not vanish identically on any punctured disk $B_r(0)\setminus\{0\}$. Let $P=(x,T)$ be a periodic Reeb orbit and $\tau:\mathbb{R}^2\to\mathbb{R}$ of class $C^1$ on some $(s_\tau,\infty)\times\mathbb{R}$. Then for every $s_0$ there are $s\ge s_0$ and $t$ with $$w\big(e^{-2\pi(s+it)}\big)\ne\mathrm{proj}\,x(\tau(s,t)).$$
--
--   So such a curve is not, on any end, a reparametrization of the trivial cylinder over $P$.
--
--   **Formalization Note** The density is `dlambdaDensity H u z`; the end is `endW H u cylEnd (s, t)`.
-- source:
--   Used for U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Theorem 2.11 and Lemma 2.12; H. Hofer, K. Wysocki, E. Zehnder, Properties of pseudoholomorphic curves in symplectisations I: asymptotics, Ann. Inst. H. Poincaré Anal. Non Linéaire 13 (1996)

import Definitions.Def_FiniteEnergyPlane_Asymptotics

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- A finite-energy curve on `D \ {0}` whose `dλ`-density `ω₀(∂ₛw, ∂ₜw)` (`w = proj H ∘ u`) does
not vanish identically on any punctured neighbourhood of `0` is not, on any end `s ≥ s₀`, of the
form `w(s, t) = proj H (x(τ(s, t)))` with `x` a Reeb orbit and `τ` of class `C¹`: for every `s₀`
there are `s ≥ s₀` and `t` with `endW(s, t) ≠ proj H (x(τ(s, t)))`. -/
theorem exists_endW_ne_proj_reeb_comp {n : ℕ} (H : V n → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V n → V n →L[ℝ] V n) (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (P : ReebOrbit H)
    (hden : ∀ r > 0, ∃ z ∈ ball (0 : ℂ) r \ {0}, dlambdaDensity H u z ≠ 0)
    (τ : ℝ × ℝ → ℝ) (sτ : ℝ) (hτ : ContDiffOn ℝ 1 τ (Set.Ioi sτ ×ˢ Set.univ)) :
    ∀ s₀ : ℝ, ∃ s ≥ s₀, ∃ t : ℝ, endW H u cylEnd (s, t) ≠ proj H (P.x (τ (s, t))) := by
  sorry

end FiniteEnergyPlane
