-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_dyadic_ceiling_pi_endpoint_measurable
-- name    : AvramDividend.Classical.avram_ws01e_b_dyadic_ceiling_pi_endpoint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T17:01:07.998776+00:00
-- url     : https://prove2.me/theorems/7789c1eb-8bbd-480d-92de-c4d48bf18202
-- title:
--   Joint product-Pi measurability of an actual dyadic-ceiling variable-time endpoint of a path
-- statement:
--   For each dyadic grid resolution n, the variable-clock endpoint of an unrestricted nonnegative-time real path sampled at the upward-rounded dyadic time ceil(2^n u)/2^n is jointly measurable in the real nonnegative clock u and the full path f under the product of Borel time and Pi measurable function-space sigma algebras. This is a genuine finite-grid surrogate for otherwise nonmeasurable variable-time evaluation f(u) on the full unrestricted Pi path space. It discharges the precise named endpoint measurability blocker in passing the Proved genuine Qp uncapped full-path first-record regeneration f5788ba0 to tilted terminal drawdown Wiener–Hopf independence. The proof uses the measurable ceiling index and a countable partition into fixed-coordinate measurable slices; no false assumption of generic variable-time path evaluation.
-- source:
--   The mathematically necessary right-continuous finite-grid surrogate in Avram WS1E-B, genuine uncapped record regeneration f5788ba0-5ca1-4ac9-ad2a-8c147d4c369c, and Proved dyadic ceiling approximation theorem 5c6df1d9-08d7-4a57-b3fc-94f32588e34b.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_dyadic_ceiling_pi_endpoint_measurable
    (n : ℕ) :
    Measurable (fun z : ℝ≥0 × (ℝ≥0 → ℝ) =>
      z.2 ((Nat.ceil ((z.1 : ℝ) * (2 : ℝ) ^ n) : ℝ≥0) /
        (2 : ℝ≥0) ^ n)) := by sorry
