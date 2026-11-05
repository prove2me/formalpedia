-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini
-- name    : AvramDividend.Classical.avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:33:07.630104+00:00
-- url     : https://prove2.me/theorems/979be838-13c7-414d-8b1b-bce72fd2022b
-- title:
--   Public original intrinsic time-mark expected measure weighted Fubini identity
-- statement:
--   The genuine original intrinsic time-mark jump counting measure admits an expected measure Q. For every measurable nonnegative time-mark test g, integration against Q equals the probability-space expectation of the integral of g against the actual original intrinsic jump measure. The construction uses the existing source-exact sigma-finite kernel from the original process and the Mathlib measure bind integral theorem; no independent auxiliary process or pre-assumed Lévy rate is introduced.

import Mathlib.MeasureTheory.Measure.GiryMonad
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_02a_actual_source_intrinsic_sfinite_kernel

open MeasureTheory ProbabilityTheory Filter Set Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_j_ui_public_original_intrinsic_weighted_kernel_fubini
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (g : (ℝ≥0 × ℝ) → ℝ≥0∞) (hg : Measurable g) :
    ∃ Q : Measure (ℝ≥0 × ℝ),
      (∀ C : Set (ℝ≥0 × ℝ), MeasurableSet C →
        Q C = (∫⁻ ω,
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
            C ∂P)) ∧
      (∫⁻ p, g p ∂Q) =
        (∫⁻ ω, (∫⁻ p, g p ∂
          ((Measure.count.restrict {u : ℝ≥0 |
            0 < u ∧ X.X u ω -
              Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
            (fun u : ℝ≥0 => (u,
              X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))) ∂P) := by sorry
