-- Prove2me | Theorems.Thm_AvramDividend_Classical_barrierRuinTime_zero_eq_iInf_positive
-- name    : AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_positive
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:25:59.128771+00:00
-- url     : https://prove2.me/theorems/8447986e-d1f0-46eb-8309-54202707fd0b
-- title:
--   Zero-barrier drawdown ruin time is the infimum of positive-barrier ruin times
-- statement:
--   For any spectrally negative Lévy path, first strictly positive drawdown occurs at the infimum of the ruin times for all strictly positive barrier thresholds. A positive drawdown strictly exceeds its half-value, giving the reverse inequality. This deterministic endpoint-limit identity is a prerequisite for passing stopped Stieltjes dividends from positive barriers to the zero barrier.
-- source:
--   Exact pathwise infimum definition of barrierRuinTime and the Proved barrierRuinTime_mono_barrier; a supporting prerequisite for AvramDividend.Classical.barrierStrategy_zero_boundary_value_identity.

import Definitions.Def_AvramDividend_Classical_ReflectionBarrier

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.barrierRuinTime_zero_eq_iInf_positive
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω) :
    barrierRuinTime X 0 ω =
      ⨅ ε : ℝ, ⨅ _ : 0 < ε, barrierRuinTime X ε ω := by sorry
