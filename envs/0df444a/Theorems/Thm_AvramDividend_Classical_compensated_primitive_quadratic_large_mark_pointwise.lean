-- Prove2me | Theorems.Thm_AvramDividend_Classical_compensated_primitive_quadratic_large_mark_pointwise
-- name    : AvramDividend.Classical.compensated_primitive_quadratic_large_mark_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T21:25:50.017181+00:00
-- url     : https://prove2.me/theorems/e98bb11e-1472-41a2-8cd5-8b9801199fd6
-- title:
--   Original compensated Lévy primitive obeys a two-regime pointwise envelope
-- statement:
--   For each actual negative jump mark y, bound the compensated primitive by quadratic jump size on (-1,0) and by absolute jump size on (-∞,-1], retaining the correct endpoint convention. Both sides are nonnegative and no integrability assumptions are required.
-- source:
--   Already Proved e44e5f40 compensated quadratic and linear primitive bounds, split at y=-1. Genuine two-regime analytic bound for the Lévy measure integrability proof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_compensated_exponential_primitive_bounds
open MeasureTheory Set AvramDividend.Classical

theorem AvramDividend.Classical.compensated_primitive_quadratic_large_mark_pointwise
    (θ y : ℝ) (hθ : 0 ≤ θ) (hy : y < 0) :
    0 ≤ (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∧
    (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ≤
      θ / 2 * min 1 (y ^ 2) +
        |(Iic (-1 : ℝ)).indicator (fun z : ℝ => z) y| := by sorry
