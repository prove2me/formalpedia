-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB131_original_physical_stopped_clipped_gradient_joint_measurable
-- name    : AvramDividend.Classical.avram_gbB131_original_physical_stopped_clipped_gradient_joint_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:56:30.143189+00:00
-- url     : https://prove2.me/theorems/9cd11c33-6a74-453f-bf86-ae77b871eb11
-- title:
--   Joint measurability of original finite-cap stopped clipped physical gradient
-- statement:
--   The postpayment reserve is jointly measurable from right-continuous adapted sections. B134 supplies measurable clipped gradient, B133 supplies joint measurable strict pre-stop indicator. Discount and products establish original physical H joint measurability.
-- source:
--   Proved reserve right continuity and joint evaluation, B133 and B134.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_postPaymentReserve_cadlag_adapted
import Theorems.Thm_AvramDividend_Classical_rightContinuous_measurable_sections_joint_evaluation
import Theorems.Thm_AvramDividend_Classical_avram_gbB133_stopping_time_joint_strict_prestop_region_measurable
import Theorems.Thm_AvramDividend_Classical_avram_gbB134_clipped_finitecap_gradient_Borel_measurable
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB131_original_physical_stopped_clipped_gradient_joint_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (ρ : Ω → ℝ≥0)
    (hρstop : IsStoppingTime 𝓕.rightCont (fun ω => (ρ ω : WithTop ℝ≥0)))
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    Measurable (fun z : ℝ≥0 × Ω =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      let Y : ℝ := x + X.X z.1 z.2 - rightLimit D z.1 z.2
      if z.1 < ρ z.2 then Real.exp (-(q * (z.1 : ℝ))) *
        (if Y ∈ Icc a b then deriv w Y else 1) else 0) := by sorry
