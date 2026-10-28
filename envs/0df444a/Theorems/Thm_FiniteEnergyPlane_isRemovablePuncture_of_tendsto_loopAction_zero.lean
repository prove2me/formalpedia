-- Prove2me | Theorems.Thm_FiniteEnergyPlane_isRemovablePuncture_of_tendsto_loopAction_zero
-- name    : FiniteEnergyPlane.isRemovablePuncture_of_tendsto_loopAction_zero
-- status  : Proved
-- author  : @Alien60
-- created : 2026-10-26T14:59:10.11304+00:00
-- url     : https://prove2.me/theorems/4ac9ef88-9361-4d33-bb63-098fbd350c51
-- title:
--   A puncture of zero charge is removable
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Write $Q(\rho)=\int_0^1 w(\gamma_\rho(t))^*\lambda$ for the action of the clockwise loop $\gamma_\rho(t)=\rho e^{-2\pi i t}$, and call $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$ the gradient bound near the puncture, where $|\nabla u|=\|Da\|+\|Dw\|$ ($\mathbb R$-invariant). Assume the gradient bound near the puncture and $Q(\rho)\to0$ as $\rho\to0^+$. Then the puncture is removable: $u$ agrees on $\dot D$ with a smooth $\tilde J$-holomorphic map $D\to\mathbb R^{2n+2}\setminus\{0\}$. (With zero charge the shifted cylinders $u(e^{-2\pi(s+it)})$ converge to constants, so $a$ stays bounded near $0$, $u$ maps a punctured neighbourhood of $0$ into a compact subset of $\mathbb R\times S$ with finite Euclidean energy, and the removable singularity theorem applies.)
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3 (removability when the charge vanishes); C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, https://arxiv.org/abs/1612.01009, Theorem 9.8 and its proof, pp. 157-160

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- (c) Zero charge: under the gradient bound, if the loop actions tend to `0` then the puncture
is removable. -/
theorem isRemovablePuncture_of_tendsto_loopAction_zero {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0)) :
    IsRemovablePuncture H J u 0 1 := by
  sorry

end FiniteEnergyPlane
