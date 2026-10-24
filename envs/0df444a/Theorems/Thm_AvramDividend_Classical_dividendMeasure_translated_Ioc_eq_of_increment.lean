-- Prove2me | Theorems.Thm_AvramDividend_Classical_dividendMeasure_translated_Ioc_eq_of_increment
-- name    : AvramDividend.Classical.dividendMeasure_translated_Ioc_eq_of_increment
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T12:01:49.444856+00:00
-- url     : https://prove2.me/theorems/34f12cc5-4baf-497f-9dcb-e4673b1859e3
-- title:
--   Stieltjes time-translation from equality of monotone right-continuous increments
-- statement:
--   For two monotone real-time dividend paths whose right limits equal their values, equality of the increments of D over [u,u+t] and E over [0,t] implies equality of their Stieltjes dividend measures over (u,u+t] and (0,t]. The lemma isolates the measure-theoretic part of the first-barrier-upcrossing time translation, enabling the Lévy-specific work to focus on path identities.

import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ioc_eq_path_increment_of_mono_rightLim

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.dividendMeasure_translated_Ioc_eq_of_increment
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (D E : ℝ≥0 → Ω → ℝ) (ω : Ω) (u t : ℝ≥0)
    (hmD : Monotone (fun r : ℝ => D r.toNNReal ω))
    (hmE : Monotone (fun r : ℝ => E r.toNNReal ω))
    (hrD : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => D v.toNNReal ω) r = D r.toNNReal ω)
    (hrE : ∀ r : ℝ,
      Function.rightLim (fun v : ℝ => E v.toNNReal ω) r = E r.toNNReal ω)
    (hinc : D (u + t) ω - D u ω = E t ω - E 0 ω) :
    (dividendMeasure D ω)
        (Set.Ioc (u : ℝ) ((u + t : ℝ≥0) : ℝ)) =
      (dividendMeasure E ω) (Set.Ioc (0 : ℝ) (t : ℝ)) := by sorry
