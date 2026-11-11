-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gfinite63_unit_occupation_integral_bounds
-- name    : AvramDividend.Classical.avram_gfinite63_unit_occupation_integral_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T23:40:10.771796+00:00
-- url     : https://prove2.me/theorems/b936af14-5d9a-4310-bc93-7288844ff2e5
-- title:
--   Measurable unit occupation of a finite time window is between zero and its duration
-- statement:
--   Deterministic Lebesgue-time bound used for original stopped cap strip: any integrable real function taking values in [0,1] has integral over (0,n) between zero and n. This supplies the uniform deterministic domination required by the original Gaussian occupation DCT.

import Mathlib
open MeasureTheory Set Filter
open scoped ENNReal NNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_gfinite63_unit_occupation_integral_bounds
    (n : ℕ) (f : ℝ → ℝ)
    (hfInt : IntegrableOn f (Ioo (0 : ℝ) (n : ℝ)) volume)
    (hf0 : ∀ t, 0 ≤ f t) (hf1 : ∀ t, f t ≤ 1) :
    0 ≤ (∫ t in Ioo (0 : ℝ) (n : ℝ), f t ∂volume) ∧
      (∫ t in Ioo (0 : ℝ) (n : ℝ), f t ∂volume) ≤ (n : ℝ) := by
  sorry
