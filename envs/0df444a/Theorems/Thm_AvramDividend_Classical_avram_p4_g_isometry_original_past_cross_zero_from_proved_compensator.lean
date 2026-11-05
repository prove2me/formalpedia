-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
-- name    : AvramDividend.Classical.avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:26:54.103097+00:00
-- url     : https://prove2.me/theorems/ca34b7de-975a-41ad-9573-e75bba5685c5
-- title:
--   Original future finite-band compensated count orthogonal to product of past measurable coefficients
-- statement:
--   For actual X intrinsic marked jump count on the original P and raw F, the compensated future finite negative mark band is orthogonal to products U*V of two F_s-measurable coefficients, with product L2 and count L2. Uses proved P2-E source rectangle law. This is the cross term needed for finite-grid predictable isometry, without a Poisson coupling or a local-martingale stopping claim.
-- source:
--   Original P2-E canonical predictable past event compensator Proved 393b03a8 + Proved P4-G original weighted finite-band zero 8? (exact name import used).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_source_intrinsic_jump_count_predictable_rectangle_compensator
import Theorems.Thm_AvramDividend_Classical_avram_p4_g_isometry_original_finite_band_weighted_L2_zero

open MeasureTheory Set AvramDividend.Classical
open scoped ENNReal NNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_g_isometry_original_past_cross_zero_from_proved_compensator
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
    (hMeas : Measurable N)
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
