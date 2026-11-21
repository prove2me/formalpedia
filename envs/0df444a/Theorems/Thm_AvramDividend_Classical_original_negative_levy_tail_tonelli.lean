-- Prove2me | Theorems.Thm_AvramDividend_Classical_original_negative_levy_tail_tonelli
-- name    : AvramDividend.Classical.original_negative_levy_tail_tonelli
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T19:47:18.57438+00:00
-- url     : https://prove2.me/theorems/4cd8a2cf-8698-4952-b7b5-a2915f3d5a9d
-- title:
--   Original negative-mark Lévy tail Tonelli identity without measure reflection
-- statement:
--   For a Lévy measure on real negative jump marks, with zero mass on [0,∞), the integrated nonnegative compensated exponential primitive over each original negative jump magnitude (-y) equals the tail integral of ν((-∞,-t)) weighted by 1-exp(-θt). Valid for potentially infinite-variation and infinite-activity measures. This is the direct original-process Tonelli source required for ψ(θ)/θ.
-- source:
--   Pinned Mathlib MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul on original ν, f(y)=-y; original goal 2fa29eaf-a835-47c5-ad9a-99fe6573547b.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.original_negative_levy_tail_tonelli
    (ν : Measure ℝ) (hν : ν (Ici (0 : ℝ)) = 0)
    (θ : ℝ) (hθ : 0 < θ) :
    (∫⁻ y : ℝ,
       ENNReal.ofReal
         (∫ t in (0 : ℝ)..(-y), 1 - Real.exp (-θ * t)) ∂ν) =
      ∫⁻ t in Ioi (0 : ℝ),
        ν (Iio (-t)) * ENNReal.ofReal (1 - Real.exp (-θ * t)) := by sorry
