-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_restrict_Ioc_measurable
-- name    : AvramDividend.Classical.dividendMeasure_restrict_Ioc_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T13:35:11.26379+00:00
-- url     : https://prove2.me/theorems/6895c621-3aaf-4437-a604-4b9274673dae
-- title:
--   Measurability of the dividend measure restricted to a fixed bounded interval
-- statement:
--   For any fixed real endpoints l and u, the random Lebesgue–Stieltjes dividend measure restricted to (l,u] is measurable as a measure-valued map of the sample point.
-- source:
--   Measure-theoretic helper for Proposition 4(i), reducing random-measure measurability on a finite horizon to fixed Ioc masses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_measurable

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_restrict_Ioc_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (l u : ℝ) :
    Measurable (fun ω => (dividendMeasure D ω).restrict (Ioc l u)) := by sorry
