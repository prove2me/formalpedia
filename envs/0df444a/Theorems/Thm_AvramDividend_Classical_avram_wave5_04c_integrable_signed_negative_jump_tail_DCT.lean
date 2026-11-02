-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
-- name    : AvramDividend.Classical.avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T17:50:05.618305+00:00
-- url     : https://prove2.me/theorems/28aa94ce-614f-4c4b-b6c4-5d80e2502cb8
-- title:
--   Vanishing large negative-jump signed L1 tail by dominated convergence
-- statement:
--   An absolutely integrable signed negative-jump kernel has vanishing integral over progressively more negative tails. The proof uses measurability of strict negative-band thresholds, eventual pointwise vanishing, domination by the original L1 envelope and Bochner dominated convergence, covering infinite activity near the origin without a global first-moment envelope at infinity.
-- source:
--   Exact original-source negative-jump generator increment integrability and polynomial primitive integrability imply this generic DCT lemma applies to both parts of the genuine ν-side approximation.

import Mathlib
set_option autoImplicit false
open MeasureTheory Filter Set
open scoped BigOperators

theorem AvramDividend.Classical.avram_wave5_04c_integrable_signed_negative_jump_tail_DCT
    (μ : Measure ℝ) (f : ℝ → ℝ)
    (hf : Measurable f)
    (hInt : IntegrableOn f (Iio (0 : ℝ)) μ) :
    Tendsto
      (fun n : ℕ =>
        ∫ y in Iio (0 : ℝ),
          if y < -(n : ℝ) then f y else 0 ∂μ)
      atTop (nhds 0) := by sorry
