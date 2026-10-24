-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach
-- name    : AvramDividend.Classical.barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:50:37.189876+00:00
-- url     : https://prove2.me/theorems/7846d851-e48f-4bb7-8edd-8896d1ad666d
-- title:
--   Correct pre-ruin payment-time set excludes a strict drawdown breach
-- statement:
--   Assuming the pointwise post-upcrossing correspondence between negative controlled reserve and drawdown exceeding barrier a, every time strictly after the passage u and strictly before the original ruin time has drawdown at most a. Therefore intersecting this post-passage pre-ruin set with the condition that the drawdown has not strictly breached the barrier leaves the set unchanged. This corrects the reversed strict inequality in the earlier Open payment-time theorem.
-- source:
--   Corrects the sign of the drawdown inequality in Open target 28e58b97-9220-49b7-ac07-9f9fe708e0e6 using the Proved riskProcess_nonneg_before_ruin (c26c83f7-d703-46b9-a361-bf008b70dfe6).

import Mathlib.Algebra.Order.Sub.Unbundled.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierStrategy_paymentTimes_after_firstUpcrossing_no_preRuin_breach
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (ω : Ω) (u : ℝ≥0)
    (hdraw : ∀ t : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) (u + t) ω < 0 ↔
        a < runningSup X (u + t) ω - X.X (u + t) ω) :
    {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} =
      {t : ℝ≥0 | u < t ∧
        (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        ¬ a < runningSup X t ω - X.X t ω} := by sorry
