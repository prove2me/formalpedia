-- Prove2me | Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_record_increment
-- name    : AvramDividend.Classical.runningSup_discounted_interval_bounds_record_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:19:53.987826+00:00
-- url     : https://prove2.me/theorems/b5f13432-7b43-44fb-a3bc-afa7877c8aca
-- title:
--   Discounted regulator payout lies between endpoint discounts multiplied by the actual running-record increase
-- statement:
--   For a spectrally negative Lévy sample path and an antitone discount weight, the genuine discounted Stieltjes running-supremum dividend paid on (s,t] is bounded by the actual record-level increment multiplied by the terminal and initial discount factors. Unlike a right-limit Stieltjes representation, the bounds refer directly to the running-supremum levels S(s) and S(t), including the origin and cases in which the interval is empty. The theorem follows from the verified interval Stieltjes bounds once the actual running-supremum right-continuity theorem is Proved.
-- source:
--   Avram Palmowski Pistorius (2007), running regulator dividend Stieltjes integral; requires separately established endpoint-weight bounds and rightLim equality. Authoring must be deferred until both imported theorem dependencies have status Proved.

import Theorems.Thm_AvramDividend_Classical_runningSup_discounted_interval_bounds_rightLim
import Theorems.Thm_AvramDividend_Classical_runningSup_realTime_rightLim_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.runningSup_discounted_interval_bounds_record_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (ω : Ω)
    (w : ℝ → ℝ≥0∞) (hw : Antitone w)
    (s t : ℝ) :
    (w t * ENNReal.ofReal
       (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω) ≤
       ∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ∧
    ((∫⁻ r, if r ∈ Set.Ioc s t then w r else 0
         ∂(dividendMeasure (runningSup X) ω)) ≤
      w s * ENNReal.ofReal
       (runningSup X t.toNNReal ω - runningSup X s.toNNReal ω)) := by sorry
