-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendStrategy_real_rightLim_measurable
-- name    : AvramDividend.Classical.dividendStrategy_real_rightLim_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T11:48:41.273535+00:00
-- url     : https://prove2.me/theorems/5557f995-8025-4dac-92f6-259b0ee1dada
-- title:
--   Measurability of the real-time extended dividend path right limit
-- statement:
--   For a dividend strategy, extend each path to real time by sending negative times to time zero using Real.toNNReal. At every fixed real r, the right limit of this monotone extended path is a measurable random variable. This is the endpoint quantity appearing in the Stieltjes function used by dividendMeasure.
-- source:
--   Measure-theoretic helper for Proposition 4(i), bridging adapted fixed-time dividend evaluations to the random Stieltjes dividend measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendStrategy_real_rightLim_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (r : ℝ) :
    Measurable (fun ω =>
      Function.rightLim (fun s : ℝ => D s.toNNReal ω) r) := by sorry
