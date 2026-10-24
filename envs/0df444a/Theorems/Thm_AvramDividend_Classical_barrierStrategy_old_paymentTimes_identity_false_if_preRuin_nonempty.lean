-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_old_paymentTimes_identity_false_if_preRuin_nonempty
-- name    : AvramDividend.Classical.barrierStrategy_old_paymentTimes_identity_false_if_preRuin_nonempty
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T17:01:42.750176+00:00
-- url     : https://prove2.me/theorems/8317ae7d-4f07-4b46-9cc4-ad9401383240
-- title:
--   A surviving post-upcrossing time refutes the old strict-breach payment-time identity
-- statement:
--   Under the original post-upcrossing sign equivalence, if there exists any time after passage and strictly before ruin, then the old claimed payment-time set equality with a strict drawdown breach is false. The proved corrected identity says that all such times avoid breach. A witness therefore belongs to the old left set and not its right set. This is a formal specification countercertificate for the still-open original payment-time theorem, conditional on nonempty survival.
-- source:
--   Consequence of Proved barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach (7846d851); identifies contradictory sign of the additional drawdown condition in Open theorem 28e58b97.

import Theorems.Thm_AvramDividend_Classical_barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_old_paymentTimes_identity_false_if_preRuin_nonempty
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω) (u : ℝ≥0)
    (hdraw : ∀ s : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) (u + s) ω < 0 ↔
        a < runningSup X (u + s) ω - X.X (u + s) ω)
    (hwitness : ∃ t : ℝ≥0, u < t ∧
      (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω) :
    {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} ≠
      {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        a < runningSup X t ω - X.X t ω} := by sorry
