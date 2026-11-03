-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
-- name    : AvramDividend.Classical.avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:22:47.716992+00:00
-- url     : https://prove2.me/theorems/a7a447fa-ec44-4883-84ca-0a38e436cf4f
-- title:
--   Exact original real paymentTimes split into the zero atom and strictly surviving NNReal physical times
-- statement:
--   Every real payment time in the exact original finite-ruin paymentTimes set is either time zero, which is included even if ruinTime=0, or a strictly positive physical time whose NNReal cast is strictly smaller than ruinTime. This is the required domain conversion to apply post-rightpayment reserve cap/solvency results to the real Stieltjes integration support. The positive ruin endpoint remains excluded; no continuity or creeping claim.
-- source:
--   Original source paymentTimes definition, NNReal and ENNReal ofReal casts.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_paymentTimes_nnreal_strict_survival_or_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (ω : Ω) (t : ℝ)
    (ht : t ∈ paymentTimes (ruinTime X x D ω)) :
    t.toNNReal = 0 ∨
      (0 < t ∧ ((t.toNNReal : ℝ≥0∞) < ruinTime X x D ω)) := by sorry
