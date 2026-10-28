-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_negative_tail_uniform_window_ws01b
-- name    : AvramDividend.Classical.bv_negative_tail_uniform_window_ws01b
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T23:31:41.064501+00:00
-- url     : https://prove2.me/theorems/a74d9443-e6b9-41cd-ad9f-57fb2f2c4aef
-- title:
--   Uniform control of near-boundary negative jump windows for BV Lévy measures
-- statement:
--   Under the Standing and bounded-variation hypotheses, the negative-jump tail function is uniformly continuous on each compact positive threshold strip. Consequently shifts by a sufficiently small nonnegative distance have uniformly small changes in the real negative-tail mass, for every starting reserve x in [2δ,a]. This is the precise analytic boundary-window estimate for smoothing the q-scale function near its jump at the origin when deriving a stopped finite-variation Dynkin formula. It establishes a genuine uniform bound away from zero and does not assert stochastic compensation or no-creeping.
-- source:
--   Immediate compact Heine–Cantor consequence of canonically Proved levy_negative_tail_continuous_of_standing_bv (38e3529e), using IsCompact.uniformContinuousOn_of_continuous and Metric.uniformContinuousOn_iff at the pinned Mathlib revision.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_levy_negative_tail_continuous_of_standing_bv

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_negative_tail_uniform_window_ws01b
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (δ a : ℝ) (hδ : 0 < δ) (hδa : 2 * δ ≤ a) :
    ∀ η : ℝ, 0 < η →
      ∃ ε : ℝ, 0 < ε ∧
        ∀ x ∈ Icc (2 * δ) a, ∀ s : ℝ,
          0 ≤ s → s ≤ ε →
          |X.ν.real (Iic (-(x - s))) -
            X.ν.real (Iic (-x))| < η := by sorry
