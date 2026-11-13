-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
-- name    : AvramDividend.Classical.avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T15:58:33.513193+00:00
-- url     : https://prove2.me/theorems/d6727b06-1b4d-4e52-8ac7-bcbc35d0dd35
-- title:
--   Countably many nonnegative-time discontinuities imply real physical-time continuity almost everywhere
-- statement:
--   The positive-real parameterisation of a nonnegative-time path is continuous at almost every positive real time if its discontinuity set on nonnegative times is countable. The real-coordinate discontinuity set lies within the countable real image of the original path discontinuities, so it is Lebesgue null.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB164_countable_nonnegative_discontinuities_ae_real_continuity
    (f : ℝ≥0 → ℝ)
    (hc : Set.Countable {u : ℝ≥0 | ¬ ContinuousAt f u})
    (n : ℕ) :
    ∀ᵐ t ∂(volume.restrict (Ioo (0 : ℝ) (n : ℝ))),
      ContinuousAt (fun r : ℝ => f (Real.toNNReal r)) t := by sorry
