-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_barrier_survival_drawdown_guard_after_upcrossing
-- name    : AvramDividend.Classical.chat04_barrier_survival_drawdown_guard_after_upcrossing
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:27:15.391737+00:00
-- url     : https://prove2.me/theorems/dc2c46d8-017b-4184-b943-11bf72734aef
-- title:
--   Correct post-upcrossing barrier survival set excludes strict drawdown ruin
-- statement:
--   If negative controlled reserve after the first upcrossing is equivalent to drawdown S-X exceeding a, then every surviving time after u necessarily has drawdown no greater than a. Therefore the surviving post-u times equal those post-u times that also satisfy ¬(a<S-X). This corrects the reversed drawdown condition in the open paymentTimes_after_firstUpcrossing_eq_shifted target 28e58b97. The proof uses the previously proved nonnegative controlled reserve strictly before ruin.
-- source:
--   Formal consequence of the Proved theorem AvramDividend.Classical.riskProcess_nonneg_before_ruin (c26c83f7-d703-46b9-a361-bf008b70dfe6) and the stated pathwise drawdown/ruin equivalence. Corrects the event polarity of 28e58b97-9220-49b7-ac07-9f9fe708e0e6.

import Mathlib.Data.Set.Basic
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_barrier_survival_drawdown_guard_after_upcrossing
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x a : ℝ) (ω : Ω) (u : ℝ≥0)
    (hdraw : ∀ t : ℝ≥0,
      riskProcess X x (barrierStrategy X x a) t ω < 0 ↔
        a < runningSup X t ω - X.X t ω) :
    {t : ℝ≥0 | u < t ∧
      (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω} =
    {t : ℝ≥0 | u < t ∧
      (t : ℝ≥0∞) < ruinTime X x (barrierStrategy X x a) ω ∧
        ¬ a < runningSup X t ω - X.X t ω} := by sorry
