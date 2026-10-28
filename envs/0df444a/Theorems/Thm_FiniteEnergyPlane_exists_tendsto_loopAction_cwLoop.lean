-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_tendsto_loopAction_cwLoop
-- name    : FiniteEnergyPlane.exists_tendsto_loopAction_cwLoop
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T14:59:09.604057+00:00
-- url     : https://prove2.me/theorems/9a8b3cbe-ddea-4653-bc97-041485d944c4
-- title:
--   The charge of a finite-energy puncture exists
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Write $Q(\rho)=\int_0^1 w(\gamma_\rho(t))^*\lambda$ for the action of the clockwise loop $\gamma_\rho(t)=\rho e^{-2\pi i t}$, and call $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$ the gradient bound near the puncture, where $|\nabla u|=\|Da\|+\|Dw\|$ ($\mathbb R$-invariant). Then the limit $Q=\lim_{\rho\to0^+}Q(\rho)$ exists in $\mathbb R$. Indeed, by Stokes $Q(\rho_1)-Q(\rho_0)$ is, up to sign, the $d\lambda$-energy $\int w^*d\lambda\ge0$ of the annulus $\rho_0<|z|<\rho_1$, so $\rho\mapsto Q(\rho)$ is monotone, and $|Q(\rho)|$ is bounded by the Hofer energy $E(u)<\infty$.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3 (Q as limit of loop actions); C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Theorem 9.8 and its proof, pp. 157-160

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- (a) The loop actions `Q(ρ) = ∫ u*λ` over the clockwise circles of radius `ρ` converge as
`ρ → 0⁺` (Stokes: `ρ ↦ Q(ρ)` is monotone, as the difference of two actions is the nonnegative
`dλ`-energy of an annulus, and bounded by the Hofer energy). -/
theorem exists_tendsto_loopAction_cwLoop {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u) :
    ∃ Q : ℝ, Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 Q) := by
  sorry

end FiniteEnergyPlane
