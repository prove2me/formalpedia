-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_singleton_second_order_bound
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_singleton_second_order_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:28:25.358357+00:00
-- url     : https://prove2.me/theorems/53d4b07f-7c44-42ae-8509-982525ad8a1f
-- title:
--   Original negative-band exactly-one-jump probability has a quadratic error
-- statement:
--   The physical probability of exactly one original negative-band jump during (0,T] is between the Lévy intensity r minus r squared and r. This follows from exact source first and factorial moments and gives a stronger finite-band single-jump rate estimate without equality-in-law.
-- source:
--   Proved original negative band cardinality, first moment and factorial moment, combined with the elementary pointwise bound K-K(K-1) <= 1_{K=1} <= K.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_singleton_second_order_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    r - r ^ 2 ≤ P.real {ω : Ω | K ω = 1} ∧
    P.real {ω : Ω | K ω = 1} ≤ r := by sorry
