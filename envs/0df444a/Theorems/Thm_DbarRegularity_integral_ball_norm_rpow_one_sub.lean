-- Prove2me | Theorems.Thm_DbarRegularity_integral_ball_norm_rpow_one_sub
-- name    : DbarRegularity.integral_ball_norm_rpow_one_sub
-- status  : Proved
-- author  : @Mazecto
-- created : 2026-10-12T17:36:37.13719+00:00
-- url     : https://prove2.me/theorems/0b1238e9-9418-486d-af43-977ae7acf426
-- title:
--   Integral of |x|^(1-d) over a ball in R^d
-- statement:
--   Let $d\ge1$ and let $|B(0,1)|$ be the Lebesgue measure of the open unit ball of $\mathbb{R}^d$. For every $r>0$ the function $x\mapsto|x|^{1-d}$ is integrable on the open ball $B(0,r)$, and
--   $$\int_{B(0,r)}|x|^{1-d}\,dx=d\,|B(0,1)|\,r .$$
--
--   The identity is a basic radial integral for estimates on kernels of size $|x|^{-d}$ near the origin.
--
--   **Formalization Note.** $\mathbb{R}^d$ is `EuclideanSpace ℝ (Fin d)` with `volume`; the power is the real power `‖x‖ ^ (1 - d : ℝ)` (at $x=0$ its value is irrelevant, the point is null). $|B(0,1)|$ is `volume.real (ball 0 1)`.
-- source:
--   E. M. Stein, Singular Integrals and Differentiability Properties of Functions, Princeton Mathematical Series 30, Princeton University Press (1970), Chapter II, § 3.2, p. 35

import Mathlib.MeasureTheory.Constructions.HaarToSphere
import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
import Mathlib.Analysis.InnerProductSpace.PiL2
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals

namespace DbarRegularity

open MeasureTheory Set Metric
open scoped ENNReal

/-- `∫_{|x| < r} |x|^{1-d} dx = d |B(0,1)| r` on `ℝ^d`, `d ≥ 1`. -/
theorem integral_ball_norm_rpow_one_sub {d : ℕ} (hd : 0 < d) (r : ℝ) (hr : 0 < r) :
    IntegrableOn (fun x : EuclideanSpace ℝ (Fin d) => ‖x‖ ^ (1 - d : ℝ)) (ball 0 r) volume ∧
      ∫ x in ball (0 : EuclideanSpace ℝ (Fin d)) r, ‖x‖ ^ (1 - d : ℝ) =
        d * volume.real (ball (0 : EuclideanSpace ℝ (Fin d)) 1) * r := by sorry

end DbarRegularity
