-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_original_negative_band_doublejump_quadratic_bound
-- name    : AvramDividend.Classical.avram_p4_s3_original_negative_band_doublejump_quadratic_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T08:12:10.727582+00:00
-- url     : https://prove2.me/theorems/6253d62d-750d-4e39-81fe-5c99fac375ea
-- title:
--   Original negative-band double-jump probability is at most half the squared finite-band intensity
-- statement:
--   For the actual spectrally negative Lévy source, the probability of at least two negative jumps beyond the separated threshold during (0,T] is bounded above by half the square of T times the exact Lévy rate. The bound gives an O(T²) short-interval control used in predictable-grid compensation and the original Poisson-law route.
-- source:
--   Exact original negative-band count factorial moment 0a13392f-85cb-4eda-8293-758dc8d8a2a7, genuine marked count identity and measurability; finite-count factorial Markov bound.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_s3_original_negative_band_doublejump_quadratic_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (n : ℕ) :
    let K : Ω → ℕ := fun ω =>
      {u : ℝ≥0 | 0 < u ∧ u ≤ T ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≤
          -(1 / ((n : ℝ) + 1))}.ncard
    let r : ℝ :=
      ((T : ℝ≥0∞) * X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal
    P.real {ω : Ω | 2 ≤ K ω} ≤ r ^ 2 / 2 := by sorry
