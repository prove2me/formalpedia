-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_normal_chart_hasLoopWind
-- name    : FiniteEnergyPlane.exists_normal_chart_hasLoopWind
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-05T20:37:37.57158+00:00
-- url     : https://prove2.me/theorems/971c59a8-21be-4a67-8e76-317661d0476e
-- title:
--   Winding number of a $J$-holomorphic curve in coordinates adapted to an immersed curve
-- statement:
--   Let $E$ be a real vector space of dimension $4$, $O\subset E$ open, and $J$ a smooth almost complex structure on $O$. Let $U,W\subset\mathbb{C}$ be open and let $u:U\to O$, $v:W\to O$ be smooth $J$-holomorphic maps, $z_0\in U$, $w_0\in W$, $u(z_0)=v(w_0)$, with $Dv(w_0)$ injective, and suppose this intersection is isolated: for some $\varepsilon>0$, the only pair $(z,w)\in B_\varepsilon(z_0)\times B_\varepsilon(w_0)$ with $u(z)=v(w)$ is $(z_0,w_0)$.
--
--   Then there are a map $\Psi:\mathbb{C}\times\mathbb{C}\to E$ with $\Psi(\zeta,0)=v(w_0+\zeta)$ for all $\zeta$, which is $C^1$ at the origin with invertible derivative there, and a map $\Xi:E\to\mathbb{C}\times\mathbb{C}$, continuous at $u(z_0)$ with $\Xi(u(z_0))=0$ and $\Psi\circ\Xi=\mathrm{id}$ near $u(z_0)$, and an integer $m\ge 1$ and $r>0$, such that for all $\rho\in(0,r)$ the loop $t\mapsto \mathrm{pr}_2\,\Xi\big(u(z_0+\rho e^{2\pi i t})\big)$ lies in $\mathbb{C}\setminus\{0\}$ with winding number $m$.
--
--   Role: measures the local intersection multiplicity of $u$ with the immersed curve $v$ by the winding number of a single complex-valued function in a coordinate system in which $v$ is the first axis.
--
--   **Formalization Note** "Smooth almost complex structure" is `JHolomorphic.IsAlmostComplexOn`, and "$J$-holomorphic" is `JHolomorphic.IsJHolomorphicOn`. The maps are functions on all of $\mathbb{C}$ and $E$, constrained only on the indicated sets; the isolation condition concerns the values of $u$ and $v$ on the two discs, which need not lie in $U$ and $W$.
-- source:
--   Cf. D. McDuff, J. Differential Geom. 34 (1991), 143-164, Section 5; M. Micallef, B. White, Ann. of Math. 141 (1995)

import Definitions.Def_FiniteEnergyPlane_Winding

namespace FiniteEnergyPlane

open Metric Filter Topology
open scoped ContDiff

/-- Let `J` be a smooth almost complex structure on an open subset `O` of a real `4`-dimensional space
`E`, and let `u`, `v` be smooth `J`-holomorphic maps from open subsets of `ℂ` to `O` with
`u(z₀) = v(w₀)` an isolated intersection and `Dv(w₀)` injective. Then there are a map
`Ψ : ℂ × ℂ → E` with `Ψ(ζ, 0) = v(w₀ + ζ)`, `C¹` at `0` with invertible derivative there, and a local
right inverse `Ξ` of `Ψ` near `u(z₀)`, continuous at `u(z₀)` with `Ξ(u(z₀)) = 0`, such that the second
component of `Ξ ∘ u` has a winding number `m ≥ 1` along all small counterclockwise circles about
`z₀`. -/
theorem exists_normal_chart_hasLoopWind {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] (hE : Module.finrank ℝ E = 4) (J : E → E →L[ℝ] E) (O : Set E)
    (hJ : JHolomorphic.IsAlmostComplexOn J O) (U W : Set ℂ) (hU : IsOpen U) (hW : IsOpen W)
    (u v : ℂ → E) (hu : ContDiffOn ℝ ∞ u U) (hv : ContDiffOn ℝ ∞ v W)
    (huO : Set.MapsTo u U O) (hvO : Set.MapsTo v W O)
    (huh : JHolomorphic.IsJHolomorphicOn J U u) (hvh : JHolomorphic.IsJHolomorphicOn J W v)
    (z₀ w₀ : ℂ) (hz₀ : z₀ ∈ U) (hw₀ : w₀ ∈ W) (h₀ : u z₀ = v w₀)
    (hvi : Function.Injective (fderiv ℝ v w₀))
    (hiso : ∃ ε > 0, ∀ z ∈ ball z₀ ε, ∀ w ∈ ball w₀ ε, u z = v w → z = z₀ ∧ w = w₀) :
    ∃ (Ψ : ℂ × ℂ → E) (Ξ : E → ℂ × ℂ) (e : (ℂ × ℂ) ≃L[ℝ] E),
      ContDiffAt ℝ 1 Ψ (0, 0) ∧ fderiv ℝ Ψ (0, 0) = (e : ℂ × ℂ →L[ℝ] E) ∧
      (∀ ζ, Ψ (ζ, 0) = v (w₀ + ζ)) ∧ ContinuousAt Ξ (u z₀) ∧ Ξ (u z₀) = (0, 0) ∧
      (∀ᶠ x in 𝓝 (u z₀), Ψ (Ξ x) = x) ∧
      ∃ m : ℕ, 1 ≤ m ∧ ∃ r > (0 : ℝ), ∀ ρ ∈ Set.Ioo 0 r,
        HasLoopWind (fun t => (Ξ (u (z₀ + ccwLoop ρ t))).2) m := by
  sorry

end FiniteEnergyPlane
