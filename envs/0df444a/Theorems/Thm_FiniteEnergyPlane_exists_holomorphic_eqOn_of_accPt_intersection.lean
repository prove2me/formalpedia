-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_holomorphic_eqOn_of_accPt_intersection
-- name    : FiniteEnergyPlane.exists_holomorphic_eqOn_of_accPt_intersection
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T21:08:47.860969+00:00
-- url     : https://prove2.me/theorems/7387c623-9026-4854-b519-f72e75697361
-- title:
--   Non-isolated intersections of pseudoholomorphic immersions are local holomorphic reparametrizations
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $U,W\subset\mathbb{C}$ be open and let $u$ on $U$ and $v$ on $W$ be finite-energy $\tilde J$-holomorphic curves which are immersions, with $u(z_0)=v(w_0)$ for some $z_0\in U$, $w_0\in W$. Suppose this intersection is not isolated: there are pairs $(z_k,w_k)\neq(z_0,w_0)$ with $u(z_k)=v(w_k)$ and $(z_k,w_k)\to(z_0,w_0)$. Then there are $\varepsilon>0$ and a map $\varphi$, holomorphic on $B_\varepsilon(z_0)$, with $\varphi(z_0)=w_0$, $\varphi'(z_0)\neq0$, $\varphi(B_\varepsilon(z_0))\subset W$ and $u=v\circ\varphi$ on $B_\varepsilon(z_0)$.
--
--   **Formalization Note** "Immersion" is: the real derivative is injective at every point of the domain. "Holomorphic on $B_\varepsilon(z_0)$" is `DifferentiableOn ℂ φ (ball z₀ ε)`, and $\varphi'(z_0)$ is `deriv φ z₀`.
-- source:
--   D. McDuff, The local behaviour of holomorphic curves in almost complex 4-manifolds, J. Differential Geom. 34 (1991), 143–164, doi:10.4310/jdg/1214446994, Lemma 2.7 (case of immersed curves)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Non-isolated intersections of pseudoholomorphic immersions (McDuff, J. Differential Geom. 34
(1991), Lemma 2.7, immersed case). Let `u` on `U` and `v` on `W` be finite-energy
`J̃`-holomorphic curves which are immersions, with `u(z₀) = v(w₀)`, and suppose this intersection
is not isolated: there are pairs `(zₖ, wₖ) ≠ (z₀, w₀)` with `u(zₖ) = v(wₖ)` and
`(zₖ, wₖ) → (z₀, w₀)`. Then near `z₀` the curve `u` is a holomorphic reparametrization of `v`:
there are `ε > 0` and a map `φ`, complex differentiable on `B_ε(z₀)`, with `φ(z₀) = w₀`,
`φ'(z₀) ≠ 0`, `φ(B_ε(z₀)) ⊆ W` and `u = v ∘ φ` on `B_ε(z₀)`. -/
theorem exists_holomorphic_eqOn_of_accPt_intersection (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W) (u v : ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hv : IsFiniteEnergyCurve H J W v)
    (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hvi : ∀ w ∈ W, Function.Injective (fderiv ℝ v w))
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (z w : ℕ → ℂ)
    (hz : Tendsto z atTop (𝓝 z₀)) (hw : Tendsto w atTop (𝓝 w₀))
    (hne : ∀ k, (z k, w k) ≠ (z₀, w₀)) (heq : ∀ k, u (z k) = v (w k)) :
    ∃ ε > 0, ∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ (ball z₀ ε) ∧ φ z₀ = w₀ ∧ deriv φ z₀ ≠ 0 ∧
      Set.MapsTo φ (ball z₀ ε) W ∧ Set.EqOn u (v ∘ φ) (ball z₀ ε) := by
  sorry

end FiniteEnergyPlane
