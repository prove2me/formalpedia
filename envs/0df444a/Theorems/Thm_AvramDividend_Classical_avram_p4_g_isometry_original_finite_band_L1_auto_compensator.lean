-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_L1_auto_compensator
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_L1_auto_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:44:01.343548+00:00
-- url     : https://prove2.me/theorems/c4ce3ed4-6cc0-4e9b-b25f-70235186a7cd
-- title:
--   Original intrinsic separated-band jump-count L1 automatically from P2-E compensator
-- statement:
--   For the actual intrinsic negative-band marked jump count of X on (s,t], the Proved original measurable count and predictable rectangle compensator together imply finite real first moment and almost-sure finite count. No extra count-measurability or rectangle-law assumption remains.
-- source:
--   P2-E original intrinsic measurable count 5cb1e247, P2-E original predictable rectangle compensator 393b03a8, P4-G original band L1 bridge ba8f57d7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_finite_band_L1_auto_compensator
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (hst : s ≤ t)
    (ε : ℝ) (hε : 0 < ε) (B : Set ℝ)
    (hB : MeasurableSet B) (hBand : B ⊆ Ioo (-1 : ℝ) (-ε))
    (hν : X.ν B < ⊤)
    (N : Ω → ℝ≥0∞)
    (hActual : N = fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc s t ×ˢ B)) :
    Integrable (fun ω => (N ω).toReal) P ∧
      (∀ᵐ ω ∂P, N ω < ⊤) := by sorry
