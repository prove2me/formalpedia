-- Prove2me | Theorems.Thm_FiniteEnergyPlane_energy_le_loopAction_of_aCoord_eq_zero
-- name    : FiniteEnergyPlane.energy_le_loopAction_of_aCoord_eq_zero
-- status  : Open
-- author  : @Mazecto
-- created : 2026-11-26T19:47:52.301473+00:00
-- url     : https://prove2.me/theorems/e7a0f4a3-dcb2-5997-acc6-39a334bf83d3
-- title:
--   Hofer energy of a punctured pseudoholomorphic disk with boundary at level zero is bounded by its boundary action
-- statement:
--   Let $S = H^{-1}(1) \subset \mathbb{R}^{2n+2}$ be strictly star-shaped, $J$ a compatible complex structure on $\xi$, and $\tilde J$ the induced almost complex structure on the symplectization $\mathbb{R} \times S \cong \mathbb{R}^{2n+2} \setminus \{0\}$. Let $\Gamma$ be a finite subset of the open unit disk $D$, and let $u : \mathbb{C} \to \mathbb{R}^{2n+2}$ be smooth on $\bar D \setminus \Gamma$, nonvanishing there, and $\tilde J$-holomorphic on $D \setminus \Gamma$. Write $a = \mathrm{aCoord} \circ u$. Suppose that $a = 0$ on the unit circle and that $a(w) \to -\infty$ as $w \to z$ for every $z \in \Gamma$. Then the Hofer energy of $u$ on $D \setminus \Gamma$ is at most the positive part of the action of its boundary loop:
--   $$E(u; D \setminus \Gamma) \le \max\Big(\int_0^1 \lambda_0\big(u(e^{2\pi i t})\big)\big[\tfrac{d}{dt}\, u(e^{2\pi i t})\big]\, dt,\ 0\Big).$$
--
--   Role: the general energy estimate for punctured disks whose boundary lies on the level $\{0\} \times S$; it reduces energy bounds for disks with boundary on a surface in $S$ to bounds on the action of the boundary loop.
--
--   Formalization Note: the right-hand side is `ENNReal.ofReal (loopAction H u (ccwLoop 1))`, where `loopAction` integrates the Liouville form along `t ↦ proj(u(e^{2πit}))`; on the circle `proj ∘ u = u` because `a = 0` there. The energy is Hofer's `sup` over admissible `φ` of `∫ u*d(φ(a)λ)`.
-- source:
--   H. Hofer, K. Wysocki, E. Zehnder, A characterisation of the tight three-sphere, Duke Math. J. 81 (1995), (26)-(27); U. Hryniewicz, Fast finite-energy planes in symplectizations and applications, Trans. AMS 364 (2012), Section 5; U. Hryniewicz, Systems of global surfaces of section for dynamically convex Reeb flows on the 3-sphere, J. Symplectic Geom. 12 (2014), Section 3.2

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Hofer energy of a punctured disk with boundary at level zero. Let `Γ` be a finite subset of the
open unit disk and let `u` be smooth on the closed unit disk minus `Γ`, avoiding `0` there, and
`J̃`-holomorphic on the open disk minus `Γ`. If the `ℝ`-coordinate `a = aCoord ∘ u` vanishes on the
unit circle and tends to `-∞` at every point of `Γ`, then the Hofer energy of `u` on the punctured
disk is at most the action `∫ u*λ` of its boundary loop `t ↦ u(e^{2πit})`. -/
theorem energy_le_loopAction_of_aCoord_eq_zero {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (Γ : Finset ℂ) (hΓ₁ : (Γ : Set ℂ) ⊆ ball 0 1)
    (u : ℂ → V n) (hu : ContDiffOn ℝ ∞ u (closedBall 0 1 \ Γ))
    (hu0 : ∀ z ∈ closedBall (0 : ℂ) 1 \ Γ, u z ≠ 0)
    (hhol : JHolomorphic.IsJHolomorphicOn (Jtilde H J) (ball 0 1 \ Γ) u)
    (hbd : ∀ z ∈ sphere (0 : ℂ) 1, aCoord H (u z) = 0)
    (hΓ : ∀ z ∈ Γ, Tendsto (fun w => aCoord H (u w)) (𝓝[≠] z) atBot) :
    energy H (ball 0 1 \ Γ) u ≤ ENNReal.ofReal (loopAction H u (ccwLoop 1)) := by
  sorry

end FiniteEnergyPlane
