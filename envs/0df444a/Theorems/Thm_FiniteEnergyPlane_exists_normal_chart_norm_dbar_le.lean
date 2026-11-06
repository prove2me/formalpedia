-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_normal_chart_norm_dbar_le
-- name    : FiniteEnergyPlane.exists_normal_chart_norm_dbar_le
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:54:05.396199+00:00
-- url     : https://prove2.me/theorems/95bbc711-57d4-42df-931e-334d434756b6
-- title:
--   A normal chart along a $J$-holomorphic immersion with $|\bar\partial g|\le M|g|$ for the normal component
-- statement:
--   Let $E$ be a real vector space of dimension $4$, $J$ a smooth almost complex structure on an open set $O\subset E$, and let $u:U\to O$, $v:W\to O$ be smooth $J$-holomorphic maps on open subsets of $\mathbb{C}$ with $u(z_0)=v(w_0)$ and $Dv(w_0)$ injective.
--
--   Then there are maps $\Psi:\mathbb{C}\times\mathbb{C}\to E$ and $\Xi:E\to\mathbb{C}\times\mathbb{C}$ and constants $R>0$, $M$ with: $\Psi(\zeta,0)=v(w_0+\zeta)$ for all $\zeta$; $\Xi\circ\Psi=\mathrm{id}$ near $0$; $\Xi(u(z_0))=0$; and on $B(z_0,R)\subset U$, the map $\Xi\circ u$ is smooth, $\Psi\circ\Xi\circ u=u$, $w_0+(\Xi\circ u)_1\in W$, and the second component $g=(\Xi\circ u)_2$ satisfies $|\partial_s g+i\,\partial_t g|\le M|g|$.
--
--   Role: in such a chart the curve $v$ is the axis $\{0\}$ in the normal coordinate, and the normal coordinate of any other $J$-holomorphic curve near it solves a perturbed Cauchy-Riemann inequality. No assumption is made on the intersections of $u$ and $v$ near the point.
-- source:
--   Cf. D. McDuff, The local behaviour of holomorphic curves in almost complex 4-manifolds, J. Differential Geom. 34 (1991), Section 2

import Definitions.Def_JHolomorphic_Setting

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

/-- Let `E` be a real vector space of dimension `4`, `J` an almost complex structure on the open set
`O ⊆ E`, and `u`, `v` smooth `J`-holomorphic maps into `O` with `u z₀ = v w₀` and `Dv(w₀)` injective.
Then there are maps `Ψ : ℂ × ℂ → E`, `Ξ : E → ℂ × ℂ` and `R > 0`, `M` with `Ψ(ζ, 0) = v(w₀ + ζ)`,
`Ξ ∘ Ψ = id` near `0` and `Ξ(u z₀) = 0`, such that on `B(z₀, R) ⊆ U` the map `Ξ ∘ u` is smooth,
`Ψ ∘ Ξ ∘ u = u`, `w₀ + (Ξ ∘ u)₁` lies in `W`, and its normal component `g = (Ξ ∘ u)₂ : B(z₀, R) → ℂ`
satisfies `|∂ₛg + i ∂ₜg| ≤ M |g|`. -/
theorem exists_normal_chart_norm_dbar_le {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 4) (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (u v : ℂ → E) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v W)
    (huO : Set.MapsTo u U O) (hvO : Set.MapsTo v W O)
    (huh : JHolomorphic.IsJHolomorphicOn J U u) (hvh : JHolomorphic.IsJHolomorphicOn J W v)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (h₀ : u z₀ = v w₀)
    (hvi : Function.Injective (fderiv ℝ v w₀)) :
    ∃ (Ψ : ℂ × ℂ → E) (Ξ : E → ℂ × ℂ) (R M : ℝ), 0 < R ∧
      (∀ ζ, Ψ (ζ, 0) = v (w₀ + ζ)) ∧
      (∀ᶠ p in 𝓝 ((0 : ℂ), (0 : ℂ)), Ξ (Ψ p) = p) ∧
      Ξ (u z₀) = (0, 0) ∧
      ContDiffOn ℝ ∞ (fun z => Ξ (u z)) (ball z₀ R) ∧
      ∀ z ∈ ball z₀ R, z ∈ U ∧ Ψ (Ξ (u z)) = u z ∧ w₀ + (Ξ (u z)).1 ∈ W ∧
        ‖fderiv ℝ (fun z => (Ξ (u z)).2) z 1 +
            Complex.I * fderiv ℝ (fun z => (Ξ (u z)).2) z Complex.I‖ ≤ M * ‖(Ξ (u z)).2‖ := by
  sorry

end FiniteEnergyPlane
