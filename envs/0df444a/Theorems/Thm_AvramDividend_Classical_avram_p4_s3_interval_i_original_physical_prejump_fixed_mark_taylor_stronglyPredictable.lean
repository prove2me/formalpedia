-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_s3_interval_i_original_physical_prejump_fixed_mark_taylor_stronglyPredictable
-- name    : AvramDividend.Classical.avram_p4_s3_interval_i_original_physical_prejump_fixed_mark_taylor_stronglyPredictable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T19:00:35.766869+00:00
-- url     : https://prove2.me/theorems/1a7b96be-b838-45d7-99c8-6c0002a2d3a0
-- title:
--   Actual original controlled pre-jump nonlinear fixed-mark Taylor integrand is strongly predictable
-- statement:
--   For the actual original Lévy path X, original physical dividend strategy D and identical right-continuous filtration, the nonlinear Itô–Meyer fixed-mark Taylor remainder at the actual post-payment pre-jump controlled reserve is strongly predictable. Measurable w suffices; its derivative is measurable. No synthetic Poisson marks, integrability or uniform bound is assumed.
-- source:
--   Public Proved original physical left-limit predictability 94ee9994 and Mathlib measurability of derivatives. Compose measurable w and derivative with actual predictable reserve at a fixed mark, and show the nonlinear difference measurable in the physical predictable sigma-algebra.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.Topology.Order.LeftRightLim
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_postPaymentReserve_leftLim_stronglyPredictable
open MeasureTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_s3_interval_i_original_physical_prejump_fixed_mark_taylor_stronglyPredictable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw : Measurable w) (z : ℝ) :
    IsStronglyPredictable 𝓕.rightCont
      (fun t ω =>
        let y := Function.leftLim
          (fun s : ℝ≥0 => x + X.X s ω - rightLimit D s ω) t
        w (y + z) - w y - z * deriv w y) := by sorry
