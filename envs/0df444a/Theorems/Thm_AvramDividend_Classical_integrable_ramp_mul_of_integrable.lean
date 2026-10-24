-- Prove2me | Theorems.Thm_AvramDividend_Classical_integrable_ramp_mul_of_integrable
-- name    : AvramDividend.Classical.integrable_ramp_mul_of_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T21:32:07.596903+00:00
-- url     : https://prove2.me/theorems/1ed04c62-86d5-489d-b4b3-62416b04bc04
-- title:
--   Multiplying an L1 real kernel by the clipped ramp preserves integrability
-- statement:
--   The clipped ramp is globally continuous and takes values between zero and one. Therefore its product with a Lebesgue integrable real function is again integrable, by the pinned Integrable.bdd_mul theorem. This supplies the integrable cut-off component for the causal convolution local-continuity argument.
-- source:
--   Pinned Integrable.bdd_mul and explicit unit upper bound for max(0,min(1,affine)).

import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_positive_ramp_cutoff_continuous_and_support
open AvramDividend.Classical MeasureTheory Set

namespace AvramDividend.Classical
theorem integrable_ramp_mul_of_integrable
    (ε : ℝ) (hε : 0 < ε) (f : ℝ → ℝ)
    (hf : Integrable f volume) :
    Integrable (fun x : ℝ => max (0 : ℝ) (min 1 ((x - ε) / ε)) * f x) volume := by sorry
end AvramDividend.Classical
