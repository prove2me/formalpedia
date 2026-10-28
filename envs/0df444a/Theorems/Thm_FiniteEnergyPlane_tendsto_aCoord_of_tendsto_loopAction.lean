-- Prove2me | Theorems.Thm_FiniteEnergyPlane_tendsto_aCoord_of_tendsto_loopAction
-- name    : FiniteEnergyPlane.tendsto_aCoord_of_tendsto_loopAction
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T14:59:11.015357+00:00
-- url     : https://prove2.me/theorems/e26bface-774e-4ef2-919d-969ee885c124
-- title:
--   The sign of the charge determines whether a puncture is positive or negative
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Write $Q(\rho)=\int_0^1 w(\gamma_\rho(t))^*\lambda$ for the action of the clockwise loop $\gamma_\rho(t)=\rho e^{-2\pi i t}$, and call $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$ the gradient bound near the puncture, where $|\nabla u|=\|Da\|+\|Dw\|$ ($\mathbb R$-invariant). Assume the gradient bound near the puncture and $Q(\rho)\to Q$. If $Q>0$ then $a(u(z))\to+\infty$ as $z\to0$, and if $Q<0$ then $a(u(z))\to-\infty$. (Along every sequence the shifted cylinders converge in $C^0_{loc}$ to $(Qs+d,\,x(Qt+c))$ in the cylinder coordinates $z=e^{-2\pi(s+it)}$, so $a$ increases by about $Q$ per unit of $s$, uniformly in $t$.)
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3 (positive and negative punctures); C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Theorem 9.8 and its proof, pp. 157-160

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- (e) The sign of the charge: under the gradient bound, `a(u(z)) → +∞` as `z → 0` if `Q > 0`
and `a(u(z)) → -∞` if `Q < 0`. -/
theorem tendsto_aCoord_of_tendsto_loopAction {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (Q : ℝ) (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q)) :
    (0 < Q → Tendsto (fun z => aCoord H (u z)) (𝓝[≠] 0) atTop) ∧
      (Q < 0 → Tendsto (fun z => aCoord H (u z)) (𝓝[≠] 0) atBot) := by
  sorry

end FiniteEnergyPlane
