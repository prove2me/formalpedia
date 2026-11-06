-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_intersection_of_tendstoCInftyLocOn
-- name    : FiniteEnergyPlane.exists_intersection_of_tendstoCInftyLocOn
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T21:08:22.128989+00:00
-- url     : https://prove2.me/theorems/7a6df4c1-4afb-4a4f-b38b-9d2f04a6a4cc
-- title:
--   Isolated intersections of pseudoholomorphic immersions persist under $C^\infty_{loc}$ convergence
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $U,W\subset\mathbb{C}$ be open and let $u$ on $U$ and $v$ on $W$ be finite-energy $\tilde J$-holomorphic curves which are immersions. Let $z_0\in U$, $w_0\in W$ with $u(z_0)=v(w_0)$ be an isolated intersection: for some $\varepsilon>0$, the only pair $(z,w)\in B_\varepsilon(z_0)\times B_\varepsilon(w_0)$ with $u(z)=v(w)$ is $(z_0,w_0)$. Let $u_k$ on $U$ and $v_k$ on $W$ be finite-energy $\tilde J$-holomorphic curves with $u_k\to u$ in $C^\infty_{loc}(U)$ and $v_k\to v$ in $C^\infty_{loc}(W)$. Then there are $z_k\to z_0$ and $w_k\to w_0$ with $u_k(z_k)=v_k(w_k)$ for all large $k$.
--
--   **Formalization Note** "Immersion" is: the real derivative is injective at every point of the domain. $C^\infty_{loc}$ convergence is `JHolomorphic.TendstoCInftyLocOn` on $U$ and on $W$. The curves $u_k,v_k$ are not assumed to be immersions.
-- source:
--   D. McDuff, The local behaviour of holomorphic curves in almost complex 4-manifolds, J. Differential Geom. 34 (1991), 143–164, doi:10.4310/jdg/1214446994, Theorem 1.1 (case of immersed curves)

import Definitions.Def_FiniteEnergyPlane_Fredholm

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Persistence of isolated intersections of pseudoholomorphic immersions in dimension four
(McDuff, J. Differential Geom. 34 (1991), Theorem 1.1, immersed case). Let `u` on `U` and `v` on
`W` be finite-energy `J̃`-holomorphic curves which are immersions, and let `u(z₀) = v(w₀)` be an
isolated intersection: near `(z₀, w₀)` there is no other pair `(z, w)` with `u(z) = v(w)`. If
`J̃`-holomorphic curves `uₖ → u` in `C^∞_loc(U)` and `vₖ → v` in `C^∞_loc(W)`, then for all large
`k` the curves `uₖ` and `vₖ` intersect, at points `zₖ → z₀` and `wₖ → w₀`. -/
theorem exists_intersection_of_tendstoCInftyLocOn (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W) (u v : ℂ → V 1) (uk vk : ℕ → ℂ → V 1)
    (hu : IsFiniteEnergyCurve H J U u) (hv : IsFiniteEnergyCurve H J W v)
    (hui : ∀ z ∈ U, Function.Injective (fderiv ℝ u z))
    (hvi : ∀ w ∈ W, Function.Injective (fderiv ℝ v w))
    (huk : ∀ k, IsFiniteEnergyCurve H J U (uk k)) (hvk : ∀ k, IsFiniteEnergyCurve H J W (vk k))
    (hcu : JHolomorphic.TendstoCInftyLocOn uk u U) (hcv : JHolomorphic.TendstoCInftyLocOn vk v W)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (h₀ : u z₀ = v w₀)
    (hiso : ∃ ε > 0, ∀ z ∈ ball z₀ ε, ∀ w ∈ ball w₀ ε, u z = v w → z = z₀ ∧ w = w₀) :
    ∃ z w : ℕ → ℂ, Tendsto z atTop (𝓝 z₀) ∧ Tendsto w atTop (𝓝 w₀) ∧
      ∀ᶠ k in atTop, uk k (z k) = vk k (w k) := by
  sorry

end FiniteEnergyPlane
