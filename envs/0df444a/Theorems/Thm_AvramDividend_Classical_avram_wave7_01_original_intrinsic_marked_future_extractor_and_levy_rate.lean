-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
-- name    : AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T12:20:25.430207+00:00
-- url     : https://prove2.me/theorems/d9b9e3c2-55dd-4d9b-82ee-f6ce49bb70c5
-- title:
--   Original Lévy intrinsic marked jump count is a measurable future-path extractor with unconditional prescribed Lévy intensity
-- statement:
--   For the unchanged actual SpectrallyNegativeLevy P 𝓕 and arbitrary measurable jump-mark B, the literal intrinsic count N_X((s,t]×B) has a Borel measurable representation as a functional of the original shifted future increment path, and its unconditional expectation equals the physical time gap times the original Lévy measure ν(B). The theorem does not assume a marked Poisson copy or a compensator identity against past events. Its measurable-extractor part and mark-specific rate part are the exact remaining nontrivial source obligations after the independently Proved W7-01 conditional factorisation; the published theorem is intentionally Open until both are proved.
-- source:
--   Same-sample transport b1721778-5db9-4e5b-96a0-c3d000566015, original source expected time-mark measure e509ef60-0d03-429a-a727-37c8bc8f1865 and Lévy–Khintchine small-time moment derivative e6973988-8944-43a3-936c-4fe904297c04 are existing Proved inputs. Requires measurable path count extraction and uniqueness of the source marked intensity from those moments. Canonical parent 393b03a8 remains Open.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_futurepath_marked_count_transport
import Theorems.Thm_AvramDividend_Classical_avram_wave6_01_original_past_expected_time_mark_occupation_measure

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_original_intrinsic_marked_future_extractor_and_levy_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ F : (ℝ≥0 → ℝ) → ℝ≥0∞,
      Measurable F ∧
      (∀ ω : Ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) =
        F (fun v : ℝ≥0 => X.X (s + v) ω - X.X s ω)) ∧
      (∫⁻ ω, ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B) ∂P) =
        ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B := by sorry
