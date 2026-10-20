-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_rightLim
-- name    : AvramDividend.Classical.runningSup_discounted_interval_bounds_rightLim
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T18:08:34.900029+00:00
-- url     : https://prove2.me/theorems/b3acf832-983a-4dee-a249-b45a9134e19c
-- title:
--   Discounted dividend reward is bracketed by terminal and initial weights times the Stieltjes record increment
-- statement:
--   For any nonincreasing nonnegative real-time discount weight w, the dividend paid by the genuine running-supremum Stieltjes measure on (s,t] is between w(t) and w(s) times the actual record increment, with record levels represented by right limits of the running supremum. This follows exactly from the proved monotone-discount integral sandwich, measurable-set constant-indicator Lebesgue integral evaluation, and the proved precise Stieltjes mass formula. It gives an executable finite-interval bound relevant to the stopped regulator valuation and holds without any Markov or scale-function exit identity.
-- source:
--   Chat 05 proved runningSup_discounted_interval_weight_bounds (6eb26a81-d7b8-4a3f-bf99-da311680c70c) and runningSup_dividendMeasure_Ioc_rightLim (842a5998-7c24-4411-aeca-81f5fd46077c). Mathlib lintegral_indicator_const, measurableSet_Ioc at pinned Mathlib revision.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_weight_bounds
import Theorems.Thm_AvramDividend_Classical_runningSup_dividendMeasure_Ioc_rightLim

open Classical MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_interval_bounds_rightLim
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (s t : ℝ) :
    (w t * ENNReal.ofReal
      (Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) t -
       Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) s) ≤
      ∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
        ∂(dividendMeasure (runningSup X) ω)) ≤
     w s * ENNReal.ofReal
      (Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) t -
       Function.rightLim (fun r : ℝ => runningSup X r.toNNReal ω) s)) := by sorry
