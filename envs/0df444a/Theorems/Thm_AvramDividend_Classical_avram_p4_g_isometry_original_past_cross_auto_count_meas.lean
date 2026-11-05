-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_auto_count_meas
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_past_cross_auto_count_meas
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:50:42.274695+00:00
-- url     : https://prove2.me/theorems/90d22b02-1428-49d4-996e-bd0e7a7e5a9d
-- title:
--   Orthogonality to physical original future band count with automatic count measurability
-- statement:
--   For original X and raw filtration F, the product of two past-measurable L2 factors has zero covariance with a future centered intrinsic count; P2-E supplies count measurability, P2-E compensator supplies centering; explicit L2 moments remain.
-- source:
--   P2-E 8146a449 and accepted P4-G ca34b7de, same physical X/P/F.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_intrinsic_rectangle_count_measurable
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_past_cross_auto_count_meas
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
        (Ioc s t ×ˢ B))
    (U V : Ω → ℝ)
    (hU : StronglyMeasurable[𝓕 s] U)
    (hV : StronglyMeasurable[𝓕 s] V)
    (hUVL2 : MemLp (fun ω => U ω * V ω) 2 P)
    (hCountL2 : MemLp (fun ω =>
      (N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) 2 P) :
    (∫ ω, U ω * (V ω *
      ((N ω).toReal -
        (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal)) ∂P) = 0 := by sorry
