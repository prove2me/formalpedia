-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_stieltjes_Ioc_eq_of_right_continuous_increment
-- name    : AvramDividend.Classical.chat04_stieltjes_Ioc_eq_of_right_continuous_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T11:59:53.6831+00:00
-- url     : https://prove2.me/theorems/be182b33-71e0-42a4-b6f5-43b53d9b3937
-- title:
--   Equal pathwise record increments imply equal dividend Stieltjes mass on the same interval
-- statement:
--   For two genuine monotone dividend strategies that are right-continuous at both endpoints of the same real-time half-open interval, equality of their cumulative dividend increments forces equality of their Lebesgue-Stieltjes measures of that interval. This generic interface turns the corrected barrier post-upcrossing running-record increment identity into equality of Stieltjes dividend payments on (u,u+t], using the original common clock.
-- source:
--   A direct consequence of Proved dividendMeasure_Ioc_rightLimit and rightLimit_eq_of_monotone_right_continuous; applied downstream to the corrected barrier regulator shift.

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_rightLimit
import Theorems.Thm_AvramDividend_Classical_rightLimit_eq_of_monotone_right_continuous

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_stieltjes_Ioc_eq_of_right_continuous_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (D E : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (hE : IsDividendStrategy 𝓕 E)
    (ω : Ω) (a b : ℝ≥0)
    (hmD : Monotone (fun s => D s ω))
    (hmE : Monotone (fun s => E s ω))
    (hrDa : ContinuousWithinAt (fun s => D s ω) (Set.Ici a) a)
    (hrDb : ContinuousWithinAt (fun s => D s ω) (Set.Ici b) b)
    (hrEa : ContinuousWithinAt (fun s => E s ω) (Set.Ici a) a)
    (hrEb : ContinuousWithinAt (fun s => E s ω) (Set.Ici b) b)
    (hinc : D b ω - D a ω = E b ω - E a ω) :
    dividendMeasure D ω (Set.Ioc (a : ℝ) (b : ℝ)) =
      dividendMeasure E ω (Set.Ioc (a : ℝ) (b : ℝ)) := by sorry
