-- Prove2me | Theorems.Thm_FiniteEnergyPlane_hasLoopWind_cylInf_eq_windInf_sub
-- name    : FiniteEnergyPlane.hasLoopWind_cylInf_eq_windInf_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-11-03T16:25:29.87274+00:00
-- url     : https://prove2.me/theorems/e5c4459a-5fef-4a8b-952d-e088da704ce6
-- title:
--   Winding of the transverse derivative on a circle around all punctures
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb{R}^4$ be a strictly star-shaped level and $J$ a smooth $d\lambda_0$-compatible complex structure on $\xi$. Let $\Gamma\subset\mathbb{C}$ be finite and $u$ a finite-energy $\tilde J$-holomorphic curve on $\mathbb{C}\setminus\Gamma$ such that $\infty$ is a positive nondegenerate puncture (Hryniewicz, Definition 2.9), $\pi\,du$ does not vanish identically, and $\mathrm{wind}_\infty(u,\infty)=k$. Let $R_0=e^{2\pi s_0}$ with $\Gamma\subset\{|z|<R_0\}$ such that $\pi\partial_su$ has no zero on $\{|z|=R_0\}$. Then the zeros of $\pi\partial_su$ in $\{|z|>R_0\}$ form a finite set $Z$, each $z\in Z$ is an isolated zero with a local index $\mathrm{ind}(z)$, and the loop $t\mapsto\pi\partial_sw(s_0,t)$ in cylindrical coordinates $e^{2\pi(s+it)}$ at $\infty$ has winding number
--   $$k-\sum_{z\in Z}\mathrm{ind}(z)$$
--   in the global frame.
--
--   **Formalization Note** The loop is the one in the definition of `HasWindInfAt H u cylInf 1`, taken at the single value $s=s_0$; local indices are `HasZeroIndex (piDs H u) z (idx z)`.
-- source:
--   U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. Amer. Math. Soc. 364 (2012), 1859–1931, arXiv:0812.4076, Section 4.6, p. 24 (winding of $\pi\cdot\partial_r w$ on the circle $|z|=R_0$); U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), arXiv:1105.2077, Section 2.2.4, formula (16)

import Definitions.Def_FiniteEnergyPlane_Compactness

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Let `u` be a finite-energy `J̃`-holomorphic curve on `ℂ \ Γ` (`Γ` finite) in the
symplectization of `S ⊂ ℝ⁴`, with a positive nondegenerate puncture at `∞` (Definition 2.9),
`π du` not identically zero and `wind_∞(u, ∞) = k`. Let `R₀ = e^{2π s₀}` be a radius with
`Γ ⊂ {|z| < R₀}` such that `π ∂ₛu` has no zero on the circle `|z| = R₀`. Then the zeros of
`π ∂ₛu` in `{|z| > R₀}` form a finite set `Z` of isolated zeros, and the loop `t ↦ π ∂ₛw(s₀, t)`
(cylindrical coordinates at `∞`, global frame) has winding number `k - Σ_{z ∈ Z} ind(z)`. -/
theorem hasLoopWind_cylInf_eq_windInf_sub (H : V 1 → ℝ) (hH : IsStrictlyStarShapedLevel H)
    (J : V 1 → V 1 →L[ℝ] V 1) (hJ : IsCompatibleXiStructure H J)
    (Γ : Finset ℂ) (u : ℂ → V 1) (hu : IsFiniteEnergyCurve H J (↑Γ)ᶜ u) (Pinf : ReebOrbit H)
    (hinf : IsNondegenerateEnd H u cylInf Pinf 1) (hne : ∃ z ∉ Γ, piDs H u z ≠ 0) (k : ℤ)
    (hk : HasWindInfAt H u cylInf 1 k) (s₀ : ℝ)
    (hΓ : ∀ z ∈ Γ, ‖z‖ < Real.exp (2 * π * s₀))
    (hcirc : ∀ z : ℂ, ‖z‖ = Real.exp (2 * π * s₀) → piDs H u z ≠ 0) :
    ∃ Z : Finset ℂ, (∀ z, z ∈ Z ↔ Real.exp (2 * π * s₀) < ‖z‖ ∧ piDs H u z = 0) ∧
      ∃ idx : ℂ → ℤ, (∀ z ∈ Z, HasZeroIndex (piDs H u) z (idx z)) ∧
        HasLoopWind (fun t => xiCoordC H (endW H u cylInf (s₀, t))
      (piXi H (endW H u cylInf (s₀, t)) (fderiv ℝ (endW H u cylInf) (s₀, t) (1, 0)))) (k - ∑ z ∈ Z, idx z) := by
  sorry

end FiniteEnergyPlane
