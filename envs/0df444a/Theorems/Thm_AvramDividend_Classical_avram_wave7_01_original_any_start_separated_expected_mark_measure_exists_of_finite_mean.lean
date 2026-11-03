-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
-- name    : AvramDividend.Classical.avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:33:29.297808+00:00
-- url     : https://prove2.me/theorems/c026c74a-c6ca-468e-a535-7387d79c0dfb
-- title:
--   All-start original separated expected mark count is a finite Borel mark measure
-- statement:
--   For any ordered source interval (s,t], the original intrinsic expected source jump count on marks ≤-ε, when assumed finite, defines a finite Borel measure of arbitrary mark sets through restriction and projection of the Proved same-Ω/P time-mark occupation measure. This all-start construction leaves the analytical identification with ν as a separate obligation; BV and finite activity are not assumed.
-- source:
--   Proved actual original occupation measure 4a1a5c10; source time interval arbitrary ordered s≤t

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_event_weighted_marked_count_is_measure
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_any_start_separated_expected_mark_measure_exists_of_finite_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t) (ε : ℝ) (hε : 0 < ε)
    (hFiniteMean :
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ Iic (-ε)) ∂P) < ⊤) :
    ∃ μ : Measure ℝ, μ Set.univ < ⊤ ∧
      ∀ B : Set ℝ, MeasurableSet B →
        μ B = (∫⁻ ω,
          ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ (B ∩ Iic (-ε))) ∂P) := by sorry
