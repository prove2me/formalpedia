-- Prove2me | Theorems.Thm_AvramDividend_Classical_stopped_lintegral_initial_record_zero
-- name    : AvramDividend.Classical.stopped_lintegral_initial_record_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:15:24.338352+00:00
-- url     : https://prove2.me/theorems/64519e4a-8962-4dcf-9cdf-8bd0eab14cdc
-- title:
--   The stopped weighted Stieltjes reward before the first positive record vanishes
-- statement:
--   For any nonnegative extended-real payment weight and any stopping horizon, the actual stopped running-supremum Stieltjes reward over (0,u] is zero when u is its finite first strict positive upcrossing time. The underlying Stieltjes measure has zero mass on that interval, and restricting it to stopped payment times preserves the null set. This permits the finite terminal record-cell reward bound to start at time zero.
-- source:
--   Use the proved zero Stieltjes mass through the first positive record. Restriction to paymentTimes preserves measure-zero sets, so the integrand vanishes almost everywhere and its lintegral is zero.

import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_zero_through_first_positive_record

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.stopped_lintegral_initial_record_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (τ : ℝ≥0∞) (f : ℝ → ℝ≥0∞) (u : ℝ≥0)
    (hu : (u : ℝ≥0∞) =
      (⨅ (s : ℝ≥0) (_ : (0 : ℝ) < X.X s ω), (s : ℝ≥0∞))) :
    (∫⁻ r in paymentTimes τ,
      if r ∈ Set.Ioc (0 : ℝ) (u : ℝ) then f r else 0
      ∂(dividendMeasure (runningSup X) ω)) = 0 := by sorry
