-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys40_original_finite_activity_bounded_predictable_mark_kernel_L1
-- name    : AvramDividend.Classical.avram_bvb_phys40_original_finite_activity_bounded_predictable_mark_kernel_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T13:14:48.264734+00:00
-- url     : https://prove2.me/theorems/130c2931-2d46-42d3-87ef-6b283eff8797
-- title:
--   Actual original predictable discounted negative-mark kernel is L1 under finite activity and a finite real reserve ceiling
-- statement:
--   Let E be any predictable subset of original time-and-sample space on which the original prepayment left-limit reserve lies below a finite real ceiling c. Let w be continuous on nonnegative reserves and identically zero on negative reserves; q≥0. For any finite predictable physical clock μ and finite original negative Levy intensity, the discounted signed kernel 1_E 1_{z<0} exp(-qt)(w(Upre+z)-w(Upre)) is integrable with respect to μ×ν_negative. This includes E containing left reserve zero, cap contact, the first ruin-causing jump and strict horizon. The jump sizes themselves require no first moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys40_original_finite_activity_bounded_predictable_mark_kernel_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ y < 0, w y = 0)
    (q : ℝ) (hq : 0 ≤ q)
    (c : ℝ) (hc : 0 ≤ c)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (hActivity : X.ν (Iio (0 : ℝ)) < ⊤)
    (E : Set (ℝ≥0 × Ω))
    (hEm : MeasurableSet[𝓕.rightCont.predictable] E)
    (hEregion : ∀ p ∈ E, Function.leftLim
      (fun s : ℝ≥0 => x + X.X s p.2 - rightLimit D s p.2) p.1 ≤ c) :
    let H : ((ℝ≥0 × Ω) × ℝ) → ℝ := fun p =>
      if p.1 ∈ E ∧ p.2 < 0 then
        Real.exp (-(q * (p.1.1 : ℝ))) *
          (w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1 + p.2) -
           w (Function.leftLim
            (fun s : ℝ≥0 => x + X.X s p.1.2 - rightLimit D s p.1.2) p.1.1))
      else 0
    (letI : MeasurableSpace (ℝ≥0 × Ω) := 𝓕.rightCont.predictable;
      Integrable H (μ.prod (X.ν.restrict (Iio (0 : ℝ))))) := by sorry
