-- Prove2me | Theorems.Thm_FiniteEnergyPlane_exists_abs_aCoord_le_of_tendsto_loopAction_zero
-- name    : FiniteEnergyPlane.exists_abs_aCoord_le_of_tendsto_loopAction_zero
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-26T17:02:01.125371+00:00
-- url     : https://prove2.me/theorems/ea08edeb-d938-41a0-8c17-23c7526a6269
-- title:
--   Zero charge keeps the symplectization coordinate bounded near a puncture
-- statement:
--   Let $S=H^{-1}(1)\subset\mathbb R^{2n+2}$ be a strictly star-shaped level with contact form $\lambda=\lambda_0|_S$ and $d\lambda$-compatible complex structure $J$ on $\xi$, and let $u=(a,w):\dot D=D\setminus\{0\}\to\mathbb R\times S\cong\mathbb R^{2n+2}\setminus\{0\}$ be a finite-energy $\tilde J$-holomorphic curve on the punctured unit disc. Write $Q(\rho)=\int_0^1 w(\gamma_\rho(t))^*\lambda$ for the action of the clockwise loop $\gamma_\rho(t)=\rho e^{-2\pi i t}$, and assume the gradient bound $|z|\,|\nabla u(z)|\le C$ for $0<|z|<r$, where $|\nabla u|=\|Da\|+\|Dw\|$. If $Q(\rho)\to0$ as $\rho\to0^+$, then the coordinate $a$ is bounded near the puncture: there are $r'>0$ and $A$ with $|a(u(z))|\le A$ for $0<|z|<r'$.
--
--   In other words, a puncture of zero charge is neither positive nor negative: $u$ does not escape to either end of the symplectization. This is a step in the zero-charge case of the asymptotic description of finite-energy punctured discs (Hofer; Wendl, Theorem 9.8).
--
--   **Formalization Note** $\mathbb R\times S$ is identified with $\mathbb R^{2n+2}\setminus\{0\}$ by $(a,x)\mapsto e^{2a}x$, and $a$ is `aCoord H`. The charge hypothesis is `Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0)`, and the gradient bound uses `gradNorm`.
-- source:
--   H. Hofer, Pseudoholomorphic curves in symplectizations with applications to the Weinstein conjecture in dimension three, Invent. Math. 114 (1993), 515-563, Section 3; C. Wendl, Lectures on Symplectic Field Theory, arXiv:1612.01009, Lemmas 9.14 and 9.17

import Definitions.Def_FiniteEnergyPlane_Setting

namespace FiniteEnergyPlane

open MeasureTheory Metric Filter Topology
open scoped ContDiff ENNReal Real

/-- Zero charge bounds the symplectization coordinate: under the gradient bound, if the loop
actions tend to `0` then `a ∘ u` is bounded on a punctured neighbourhood of the puncture. -/
theorem exists_abs_aCoord_le_of_tendsto_loopAction_zero {n : ℕ} (H : V n → ℝ)
    (hH : IsStrictlyStarShapedLevel H) (J : V n → V n →L[ℝ] V n)
    (hJ : IsCompatibleXiStructure H J) (u : ℂ → V n)
    (hu : IsFiniteEnergyCurve H J (ball 0 1 \ {0}) u)
    (hG : ∃ r : ℝ, 0 < r ∧ ∃ C : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → ‖z‖ * gradNorm H u z ≤ C)
    (hQ : Tendsto (fun ρ => loopAction H u (cwLoop 0 ρ)) (𝓝[>] 0) (𝓝 0)) :
    ∃ r : ℝ, 0 < r ∧ ∃ A : ℝ, ∀ z : ℂ, z ≠ 0 → ‖z‖ < r → |aCoord H (u z)| ≤ A := by
  sorry

end FiniteEnergyPlane
