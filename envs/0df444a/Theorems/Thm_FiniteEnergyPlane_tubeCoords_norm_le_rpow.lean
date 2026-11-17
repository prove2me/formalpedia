-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tubeCoords_norm_le_rpow
-- name    : FiniteEnergyPlane.tubeCoords_norm_le_rpow
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-16T21:59:59.263262+00:00
-- url     : https://prove2.me/theorems/4042514d-ed60-472d-b395-6485c1cad785
-- title:
--   Decay of the normal coordinate of a graph in a tube around a plane
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^4$, $P = (x, T)$ a periodic Reeb orbit and $\pi$ the radial projection to $S$. Let $u, f : \mathbb{C} \to \mathbb{R}^4$, $N(z) : \mathbb{C} \to \mathbb{R}^4$ real linear, $\psi : \mathbb{C} \to \mathbb{C}$ differentiable and $v : \mathbb{C} \to \mathbb{C}$, and let $\delta < 0$, $r_0, C_0, R_0 \in \mathbb{R}$. Assume:
--   - for $|\zeta| \ge R_0$ and $|w| \le r_0$: $|w| \le C_0\big(\operatorname{dist}(\pi(u(\zeta) + N(\zeta) w), x(\mathbb{R})) + \operatorname{dist}(\pi(u(\zeta)), x(\mathbb{R}))\big)$;
--   - there are $\mu_u < \delta$, $C_u$ with $\operatorname{dist}(\pi(u(z)), x(\mathbb{R})) \le C_u (1 + |z|)^{\mu_u/2\pi}$ for all $z$, and likewise $\mu_f < \delta$, $C_f$ for $f$;
--   - $f(z) = u(\psi(z)) + N(\psi(z)) v(z)$ and $|v(z)| \le r_0$ for all $z$, and $\|D\psi(z) - \mathrm{id}\| \le 1/2$ for all $z$.
--
--   Then there are $\mu < \delta$ and $C$ with $|v(z)| \le C (1 + |z|)^{\mu/2\pi}$ for all $z \in \mathbb{C}$.
--
--   Role: the $C^0$ decay, strictly faster than the window rate, of the normal coordinate of a plane written as a graph over another plane in a tube.
--
--   Formalization note: $\mathbb{R}^4$ is `V 1`, $\pi$ is `proj H`, distances to the orbit are `infDist _ (Set.range P.x)`.
-- source:
--   Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 6

import Definitions.Def_FiniteEnergyPlane_TubeFamily

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Decay of the normal coordinate of a graph in a tube. Suppose that for `|ζ| ≥ R₀` and
`|w| ≤ r₀` the normal coordinate satisfies
`|w| ≤ C₀ (dist(proj (u ζ + N ζ w), P) + dist(proj (u ζ), P))`, that `u` and `f` approach `P`
like `(1 + |z|)^{μ/2π}` for some `μ < δ` (one exponent each), with `δ < 0`, and that
`f z = u (ψ z) + N (ψ z) (v z)` with `|v| ≤ r₀` and `‖Dψ - id‖ ≤ 1/2`. Then
`|v z| ≤ C (1 + |z|)^{μ/2π}` for some `μ < δ` and `C`. -/
theorem tubeCoords_norm_le_rpow (H : V 1 → ℝ) (P : ReebOrbit H) (u : ℂ → V 1)
    (N : ℂ → ℂ →L[ℝ] V 1) (f : ℂ → V 1) (r₀ C₀ R₀ : ℝ)
    (hnorm : ∀ ζ w : ℂ, R₀ ≤ ‖ζ‖ → ‖w‖ ≤ r₀ →
      ‖w‖ ≤ C₀ * (infDist (proj H (u ζ + N ζ w)) (Set.range P.x) +
        infDist (proj H (u ζ)) (Set.range P.x)))
    (δ : ℝ) (hδ : δ < 0)
    (hδu : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (u z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (hδf : ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, infDist (proj H (f z)) (Set.range P.x) ≤
      C * (1 + ‖z‖) ^ (μ / (2 * π)))
    (ψ : ℂ → ℂ) (hψ : Differentiable ℝ ψ) (v : ℂ → ℂ) (hvr : ∀ z, ‖v z‖ ≤ r₀)
    (hf : ∀ z, f z = u (ψ z) + N (ψ z) (v z))
    (hDψ : ∀ z, ‖fderiv ℝ ψ z - ContinuousLinearMap.id ℝ ℂ‖ ≤ 1 / 2) :
    ∃ μ < δ, ∃ C : ℝ, ∀ z : ℂ, ‖v z‖ ≤ C * (1 + ‖z‖) ^ (μ / (2 * π)) := by
  sorry

end FiniteEnergyPlane
