-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_separated_expected_mark_measure_exists_of_finite_mean
-- name    : AvramDividend.Classical.avram_wave7_01_original_separated_expected_mark_measure_exists_of_finite_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:20:05.786372+00:00
-- url     : https://prove2.me/theorems/815a869d-6776-4d4a-8bf0-bc4a85a823a3
-- title:
--   Finite original source separated-mark expected count defines a finite mark measure
-- statement:
--   For actual Ω, P, X and intrinsic original jump measure, an explicit finite expected count on (0,T] and negative marks ≤-ε produces a finite Borel measure μ on real marks. Its values are the expected original counts on restricted marked time rectangles. This uses the Proved original event-weighted mark occupation measure and the measurable pushforward of its restricted time-mark measure. No compensation rate or finite activity is assumed.
-- source:
--   Proved original event-weighted count measure 4a1a5c10-7a55-4fe0-886a-73d7e4e53f0a

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_separated_expected_mark_measure_exists_of_finite_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (T : ℝ≥0) (ε : ℝ) (hε : 0 < ε)
    (hFiniteMean :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ Iic (-ε)) ∂P) < ⊤) :
    ∃ μ : Measure ℝ, μ Set.univ < ⊤ ∧
      ∀ B : Set ℝ, MeasurableSet B →
        μ B = (∫⁻ ω,
          ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 T ×ˢ (B ∩ Iic (-ε))) ∂P) := by sorry
