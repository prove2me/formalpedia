-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_qDiscount_interval_weight_bounds
-- name    : AvramDividend.Classical.runningSup_qDiscount_interval_weight_bounds
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:12:15.36012+00:00
-- url     : https://prove2.me/theorems/006b3d58-c648-43f8-a16d-8c58934c136e
-- title:
--   Avram exponential q-discounted dividend rewards obey endpoint-weight bounds on each payment interval
-- statement:
--   For q≥0, the exponential discount t↦ENNReal.ofReal(exp(-q t)) is antitone. Applying the proved general monotone-weight interval inequality gives lower and upper bounds for the actual expected discounted running-supremum dividend on (s,t] by replacing every payment discount with its terminal or initial discount factor. This is an exact instance with the q-discount used in barrierSupValue, requiring no extra path continuity, Markov, or scale function assumptions.
-- source:
--   Avram Palmowski Pistorius (2007), exponential q-discounted running regulator dividends; remotely Proved runningSup_discounted_interval_weight_bounds 6eb26a81-d7b8-4a3f-bf99-da311680c70c, pinned Mathlib Real.exp_le_exp_of_le and ENNReal.ofReal_le_ofReal.

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_weight_bounds

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_qDiscount_interval_weight_bounds
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (q : ℝ) (hq : 0 ≤ q) (s t : ℝ) :
    ((∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * t))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω))) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * r))) else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
     (∫⁻ r, if r ∈ Set.Ioc s t
        then ENNReal.ofReal (Real.exp (-(q * s))) else 0
        ∂(dividendMeasure (runningSup X) ω))) := by sorry
