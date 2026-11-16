-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_physical_marked_future_count_independent_of_any_past_observable_20261115
-- name    : AvramDividend.Classical.avram_a25_original_physical_marked_future_count_independent_of_any_past_observable_20261115
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T15:19:32.181806+00:00
-- url     : https://prove2.me/theorems/0832c67e-375f-4fa4-964b-4dd3efbec3d5
-- title:
--   Physical Borel marked future jump count independent of every arbitrary measurable past history observable
-- statement:
--   For the original Lévy source, any measurable Borel marked jump count on the deterministic future interval (s,s+T] is independent under the original P of any random variable H measurable with respect to the original filtration 𝓕s, with arbitrary measurable codomain E. The proved future count extractor d9b9e3c2 identifies the actual source count as a measurable function of shifted future path. The proved future-path independence ws01b 36ce4b40 then directly gives IndepFun. This strong source result is the Markov/independent increment input for finite-dimensional joint laws and exact Poisson physical jump count distribution.
-- source:
--   Proved original intrinsic Borel future marked count extraction d9b9e3c2 and measured future functional independence 36ce4b40.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a25_original_physical_marked_future_count_independent_of_any_past_observable_20261115
    {Ω E : Type*} [mΩ : MeasurableSpace Ω] [MeasurableSpace E]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s T : ℝ≥0) (B : Set ℝ) (hB : MeasurableSet B)
    (H : Ω → E) (hH : Measurable[𝓕 s] H) :
    IndepFun H (fun ω : Ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s (s + T) ×ˢ B)) P := by sorry
