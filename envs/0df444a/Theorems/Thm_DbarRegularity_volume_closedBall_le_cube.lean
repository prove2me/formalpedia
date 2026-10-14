-- Prove2me | Theorems.Thm_DbarRegularity_volume_closedBall_le_cube
-- name    : DbarRegularity.volume_closedBall_le_cube
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-11T23:45:57.502408+00:00
-- url     : https://prove2.me/theorems/7a04f58c-5733-4e92-8c22-d9083627198c
-- title:
--   Volume of a Euclidean ball is at most that of the enclosing cube
-- statement:
--   For every $x\in\mathbb{R}^d$ and $\rho\in\mathbb{R}$, the closed Euclidean ball $\bar B(x,\rho)$ satisfies
--   $$|\bar B(x,\rho)|\le\big((2\rho)^+\big)^d,$$
--   where $|\cdot|$ is Lebesgue measure and $t^+=\max(t,0)$; that is, the ball has at most the volume of a cube of side $2\rho$.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with Lebesgue measure `volume` (values in `ℝ≥0∞`), $\bar B(x,\rho)$ is `Metric.closedBall x ρ`, and $((2\rho)^+)^d$ is `ENNReal.ofReal (2 * ρ) ^ d`. The statement imports `Definitions.Def_DbarRegularity_Setting` for the ambient setting only.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter I, § 3.2, p. 16

import Definitions.Def_DbarRegularity_Setting

namespace DbarRegularity

open MeasureTheory Metric
open scoped ENNReal

/-- The Lebesgue measure of the closed Euclidean ball of radius `ρ` in `ℝ^d` is at most
`(2ρ)^d`, the volume of a cube of side `2ρ`. -/
theorem volume_closedBall_le_cube {d : ℕ} (x : EuclideanSpace ℝ (Fin d)) {ρ : ℝ} :
    volume (closedBall x ρ) ≤ ENNReal.ofReal (2 * ρ) ^ d := by sorry

end DbarRegularity
