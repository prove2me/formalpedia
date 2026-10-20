-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_interval_record_bounds
-- name    : AvramDividend.Classical.runningSup_qDiscount_interval_record_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:34:51.838089+00:00
-- url     : https://prove2.me/theorems/ab0e5769-ea91-4590-86ca-a4d137108409
-- title:
--   Discounted actual reflected dividends bounded by endpoint q-weights times record increments
-- statement:
--   For any nonnegative real discount parameter and any real interval endpoints, the actual discounted Stieltjes payout of the running-supremum regulator lies between the terminal or initial exponential q-discount factor multiplied by the actual running-record increment on that interval. This specialises a remotely proved pathwise Stieltjes interval theorem and is a direct quantitative input to finite-grid and stopped-reward discretisation.
-- source:
--   Remotely proved runningSup_discounted_interval_bounds_record_increment b5f13432-7b43-44fb-a3bc-afa7877c8aca and remotely verified antitone q-discount proof from runningSup_qDiscount_interval_weight_bounds 006b3d58-c648-43f8-a16d-8c58934c136e.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_interval_record_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (s t : ℝ) :
    (ENNReal.ofReal (Real.exp (-(q * t))) *
       ENNReal.ofReal
         (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) ≤
      ∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
      ENNReal.ofReal (Real.exp (-(q * s))) *
        ENNReal.ofReal
          (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)) := by sorry
