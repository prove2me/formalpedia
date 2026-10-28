-- Prove2me | Theorems.Thm_FiniteEnergyPlane_lintegral_energyDensity_annulus_le_loopAction
-- name    : FiniteEnergyPlane.lintegral_energyDensity_annulus_le_loopAction
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T20:45:18.130024+00:00
-- url     : https://prove2.me/theorems/8ff6f81c-8835-4eeb-8311-e861725b3a32
-- title:
--   Annulus energy between level-separated circles is bounded by the loop actions
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. For a level $A\in\mathbb R$ let $\varphi_A(s)=\chi(s-A)^2$, where $\chi$ is Mathlib's smooth transition function ($\chi=0$ on $(-\infty,0]$, $\chi=1$ on $[1,\infty)$), so $\varphi_A$ is an admissible function in Hofer's energy. Let $0<\rho_2<\rho_1<1$, and suppose that on each circle $|z|=\rho_i$ either $a\circ u\le A$ everywhere or $a\circ u\ge A+1$ everywhere. Then
--   $$\int_{\rho_2\le|z|<\rho_1} u^*d(\varphi_A(a)\lambda)\;\le\;|Q(\rho_1)|+|Q(\rho_2)|,$$
--   where $Q(\rho)=\int_0^1 w(\gamma_\rho(t))^*\lambda$ is the action of the clockwise loop $\gamma_\rho(t)=\rho e^{-2\pi i t}$.
--
--   In words: the Hofer-energy integrand at level $A$ over an annulus whose boundary circles avoid the slab $A<a<A+1$ is controlled by the actions of the two boundary loops. This is a step in the zero-charge case of the asymptotic description of finite-energy punctured discs (Hofer; Wendl, Theorem 9.8).
--
--   **Formalization Note** $\mathbb R\times S$ is identified with $\mathbb R^{2n+2}\setminus\{0\}$ by $(a,x)\mapsto e^{2a}x$, and $a$ is `aCoord H`. The integrand of $u^*d(\varphi(a)\lambda)$ with respect to $ds\wedge dt$ is `energyDensity H φ u`; the integral is the lower Lebesgue integral of its positive part over `ball 0 ρ₁ \ ball 0 ρ₂`, and $Q(\rho)$ is `loopAction H u (cwLoop 0 ρ)`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lemmas 9.14 and 9.17

import Definitions.Def_FiniteEnergyPlane_Setting
import Mathlib.Analysis.SpecialFunctions.SmoothTransition

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Annulus energy between level-separated circles is bounded by the loop actions. Let
`φ_A(s) = smoothTransition(s - A)²` (`0` for `s ≤ A`, `1` for `s ≥ A + 1`), and let
`0 < ρ₂ < ρ₁ < 1` be radii such that on each of the two circles `‖z‖ = ρᵢ` the coordinate
`a = aCoord ∘ u` stays either `≤ A` or `≥ A + 1`. Then the integral of the energy density
`u*d(φ_A(a) λ)` over the annulus `ρ₂ ≤ ‖z‖ < ρ₁` is at most `|Q(ρ₁)| + |Q(ρ₂)|`, where `Q` is the
action of the clockwise loop. -/
theorem lintegral_energyDensity_annulus_le_loopAction {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) (A ρ₁ ρ₂ : ℝ) (h₂ : 0 < ρ₂)
    (h₂₁ : ρ₂ < ρ₁) (h₁ : ρ₁ < 1)
    (hc₁ : (∀ z : ℂ, ‖z‖ = ρ₁ → aCoord H (u z) ≤ A) ∨
      (∀ z : ℂ, ‖z‖ = ρ₁ → A + 1 ≤ aCoord H (u z)))
    (hc₂ : (∀ z : ℂ, ‖z‖ = ρ₂ → aCoord H (u z) ≤ A) ∨
      (∀ z : ℂ, ‖z‖ = ρ₂ → A + 1 ≤ aCoord H (u z))) :
    ∫⁻ z in ball 0 ρ₁ \ ball 0 ρ₂,
        ENNReal.ofReal (energyDensity H (fun s => Real.smoothTransition (s - A) ^ 2) u z) ≤
      ENNReal.ofReal (|loopAction H u (cwLoop 0 ρ₁)| + |loopAction H u (cwLoop 0 ρ₂)|) := by
  sorry

end FiniteEnergyPlane
