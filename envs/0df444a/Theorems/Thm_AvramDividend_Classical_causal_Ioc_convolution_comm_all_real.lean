-- Prove2me | Theorems.Thm_AvramDividend_Classical_causal_Ioc_convolution_comm_all_real
-- name    : AvramDividend.Classical.causal_Ioc_convolution_comm_all_real
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:45:02.12036+00:00
-- url     : https://prove2.me/theorems/34162b78-b1d3-4a38-9a68-1623d66ae30c
-- title:
--   Causal positive-interval convolution commutes at every real endpoint
-- statement:
--   The two orientations of the positive-interval convolution have equal integrals for every real x. For nonnegative x invoke the proved commutativity identity; for negative x the interval (0,x] is empty. Unifies the orientation used by the exponential-tilt recurrence with the monotonicity and renewal-power recurrences without extra domain assumptions.
-- source:
--   Proved positive_Ioc_causal_convolution_comm_real plus empty-interval argument.

import Theorems.Thm_AvramDividend_Classical_positive_Ioc_causal_convolution_comm_real
open AvramDividend.Classical MeasureTheory Set

theorem AvramDividend.Classical.causal_Ioc_convolution_comm_all_real
    (f g : ℝ → ℝ) (x : ℝ) :
    (∫ s in Ioc (0 : ℝ) x, f s * g (x - s) ∂volume) =
      ∫ s in Ioc (0 : ℝ) x, g s * f (x - s) ∂volume := by sorry
