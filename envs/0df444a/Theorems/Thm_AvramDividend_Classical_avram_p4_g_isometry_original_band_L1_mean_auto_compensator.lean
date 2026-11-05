-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_band_L1_mean_auto_compensator
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_band_L1_mean_auto_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T18:46:07.623137+00:00
-- url     : https://prove2.me/theorems/6b63f3c7-0533-4d2a-8b21-1fcfa1085e8a
-- title:
--   Original physical finite-band count integrability and exact real first moment automatically
-- statement:
--   On the same X/P/F and intrinsic NX, the original P2-E predictable rectangle law at all past events and measurability imply both L1 of real finite-band counts and the exact mean (t-s)ν(B), with almost sure count finiteness. No external abstract Poisson process is used.
-- source:
--   Certified original P2-E count-measurable 5cb1e247, rectangle compensator 393b03a8 and original P4-G finite-band L1 bridge ba8f57d7.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_original_intrinsic_marked_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_count_L1_of_rectangle

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_band_L1_mean_auto_compensator
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
      (∫ ω, (N ω).toReal ∂P) =
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal ∧
      (∀ᵐ ω ∂P, N ω < ⊤) := by sorry
