-- Prove2me | Theorems.Thm_CourierDispatch_Exogenous_batch_trip_mean
-- name    : CourierDispatch.Exogenous.batch_trip_mean
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-15T23:12:24.339111+00:00
-- url     : https://prove2.me/theorems/d16873d8-64b9-4dab-9795-6f2f2b3fc579
-- title:
--   (8), first moment, p. 11 — the batch trip has E[X_B] = (128/(45π) + 4/3) r, giving μ_B (9)
-- statement:
--   Let $r>0$ and let $U,U'$ be independent, each uniformly distributed on the disk of radius $r$ centred at the facility. A batch trip goes from the facility to one customer, to the other, and back, so its length is
--   $$X_B=\|U\|+\|U-U'\|+\|U'\| .$$
--   Then $X_B$ is integrable and
--   $$\mathbb E[X_B]=\Big(\frac{128}{45\pi}+\frac43\Big)r,\qquad\text{hence}\qquad \frac1{\mathbb E[X_B]}=\frac{45\pi}{4r(32+15\pi)}=\mu_B .$$
--
--   The term $128r/(45\pi)$ is the classical mean distance between two independent uniform points of a disk. The result grounds the batch service rate $\mu_B$.
--
--   **Formalization Note** The pair $(U,U')$ has the product law of two copies of the uniform law on the disk. The paper's second moment $\mathbb E[X_B^2]\approx 5.428r^2$ is a numerical value and is not stated.
-- source:
--   Chen, Hu, Courier Dispatch in On-Demand Delivery, SSRN 3675063 (version of 2022-09-21), p. 11, (8) (first moment), (9)

import Mathlib
import Definitions.Def_CourierDispatch_Exogenous_Setting
import Definitions.Def_CourierDispatch_Exogenous_DiskLaw

namespace CourierDispatch.Exogenous

/-- (8), first moment, p. 11: for two independent uniform points `U, U'` of the disk of radius `r`,
the batch trip `X_B = ‖U‖ + ‖U − U'‖ + ‖U'‖` is integrable and has `E[X_B] = (128/(45π) + 4/3) r`; hence
`μ_B = 1/E[X_B]` (9). -/
theorem batch_trip_mean (r : ℝ) (hr : 0 < r) :
    MeasureTheory.Integrable (fun p : EuclideanSpace ℝ (Fin 2) × EuclideanSpace ℝ (Fin 2) =>
      ‖p.1‖ + ‖p.1 - p.2‖ + ‖p.2‖) ((diskLaw r).prod (diskLaw r)) ∧
    (∫ p, ‖p.1‖ + ‖p.1 - p.2‖ + ‖p.2‖ ∂((diskLaw r).prod (diskLaw r))) =
      (128 / (45 * Real.pi) + 4 / 3) * r ∧
    1 / (∫ p, ‖p.1‖ + ‖p.1 - p.2‖ + ‖p.2‖ ∂((diskLaw r).prod (diskLaw r))) = muB r := by sorry

end CourierDispatch.Exogenous
