-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_pos_le_lintegral_energyDensity_annulus
-- name    : FiniteEnergyPlane.exists_pos_le_lintegral_energyDensity_annulus
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T20:45:19.147209+00:00
-- url     : https://prove2.me/theorems/06d2e6f6-e484-488b-9d0a-8341e5bbb466
-- title:
--   Crossing a unit slab of the symplectization costs a definite amount of energy
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. For a level $A\in\mathbb R$ let $\varphi_A(s)=\chi(s-A)^2$, where $\chi$ is Mathlib's smooth transition function ($\chi=0$ on $(-\infty,0]$, $\chi=1$ on $[1,\infty)$). Then there is a constant $c>0$ with the following property. For every level $A$ and all radii $0<\rho_2<\rho_1<1$ such that $a\circ u\le A$ on one of the circles $|z|=\rho_i$ and $a\circ u\ge A+1$ on the other,
--   $$\int_{\rho_2\le|z|<\rho_1} u^*d(\varphi_A(a)\lambda)\;\ge\;c .$$
--
--   In words: whenever $u$ crosses a unit slab $A\le a\le A+1$ of the symplectization between two circles about the puncture, the Hofer-energy integrand at that level over the annulus is at least $c$, and $c$ does not depend on the level $A$ or on the radii. This is a step in the zero-charge case of the asymptotic description of finite-energy punctured discs (Hofer; Wendl, Theorem 9.8).
--
--   **Formalization Note** $\mathbb R\times S$ is identified with $\mathbb R^{2n+2}\setminus\{0\}$ by $(a,x)\mapsto e^{2a}x$, and $a$ is `aCoord H`. The integrand of $u^*d(\varphi(a)\lambda)$ with respect to $ds\wedge dt$ is `energyDensity H φ u`; the integral is the lower Lebesgue integral of its positive part over `ball 0 ρ₁ \ ball 0 ρ₂`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lemmas 9.14 and 9.17

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Crossing a unit slab costs a definite amount of energy, uniformly in the level. Let
`φ_A(s) = smoothTransition(s - A)²`. There is `c > 0` such that for every level `A` and all radii
`0 < ρ₂ < ρ₁ < 1` for which `a = aCoord ∘ u` is `≤ A` on one of the circles `‖z‖ = ρᵢ` and
`≥ A + 1` on the other, the energy density `u*d(φ_A(a) λ)` integrates to at least `c` over the
annulus `ρ₂ ≤ ‖z‖ < ρ₁`. -/
theorem exists_pos_le_lintegral_energyDensity_annulus {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ c : ℝ, 0 < c ∧ ∀ A ρ₁ ρ₂ : ℝ, 0 < ρ₂ → ρ₂ < ρ₁ → ρ₁ < 1 →
      (((∀ z : ℂ, ‖z‖ = ρ₁ → aCoord H (u z) ≤ A) ∧
          ∀ z : ℂ, ‖z‖ = ρ₂ → A + 1 ≤ aCoord H (u z)) ∨
        ((∀ z : ℂ, ‖z‖ = ρ₁ → A + 1 ≤ aCoord H (u z)) ∧
          ∀ z : ℂ, ‖z‖ = ρ₂ → aCoord H (u z) ≤ A)) →
      ENNReal.ofReal c ≤ ∫⁻ z in ball 0 ρ₁ \ ball 0 ρ₂,
        ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) := by
  sorry

end FiniteEnergyPlane
