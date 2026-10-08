-- Prove2me | Theorems.Thm_AvramDividend_Classical_small_negative_jump_deficit_integral_of_integrable
-- name    : AvramDividend.Classical.small_negative_jump_deficit_integral_of_integrable
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T12:33:24.65062+00:00
-- url     : https://prove2.me/theorems/ec0957a0-e382-4f57-845b-ec5368f5f855
-- title:
--   Small-negative-jump normalized integral tends to zero under finite first absolute moment
-- statement:
--   For an arbitrary measure ν, finiteness of the negative first moment on (-1,0) suffices for the normalized integral of (1-exp(theta*y))/theta over that set to vanish as theta tends to infinity. The support and integrand-measurability conditions are derived automatically from the measurable restriction and real exponential, closing the dominated-convergence argument for bounded-variation small jumps.
-- source:
--   Compose small_negative_jump_deficit_integral_tendsto_zero with pinned ae_restrict_of_forall_mem in Mathlib/MeasureTheory/Measure/Restrict.lean and measurability of real exponential. The parent DCT theorem is a separately authored proof child.

import Mathlib
open Filter MeasureTheory Set

namespace AvramDividend.Classical

theorem small_negative_jump_deficit_integral_of_integrable
    (ν : Measure ℝ)
    (hint : IntegrableOn (fun y : ℝ => -y) (Ioo (-1 : ℝ) 0) ν) :
    Tendsto
      (fun θ : ℝ => ∫ y in Ioo (-1 : ℝ) 0,
        (1 - Real.exp (θ * y)) / θ ∂ν)
      atTop (nhds (0 : ℝ)) := by
  sorry

end AvramDividend.Classical
