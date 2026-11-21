-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovecap_large_negative_raw_levy_integral_nonpos
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovecap_large_negative_raw_levy_integral_nonpos
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:44:25.821415+00:00
-- url     : https://prove2.me/theorems/5233c684-63fc-478d-942f-0aa9af0ebb9c
-- title:
--   Actual finitecap negative Lévy large-mark raw uncompensated generator integral is nonpositive above cap
-- statement:
--   Original source-compensated finitecap infinite-negative-activity jump generator: the large negative Lévy marks z≤-1 are never derivative-compensated. Above cap y>C, the raw caplinear mark loss V(y+z)-V(y) is pointwise nonpositive for all negative z by Proved 22675bab, including ruin overshoots. Therefore its genuine original Lévy integral restricted to large negative marks is nonpositive whenever integrable. This cleanly isolates the heavy-tail untruncated large-jump sign; it neither assumes a finite first negative-mark moment nor substitutes a physically false entire-mark compensated integral. Integrability hI is left explicit because the large-jump rate alone does not give an absolute first-moment envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovecap_large_negative_raw_levy_integral_nonpos
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y : ℝ) (hy : C.toReal < y)
    (hI : Integrable (fun z : ℝ =>
      (if y + z ≤ C.toReal then w (y + z)
       else w C.toReal + (y + z - C.toReal)) -
        (w C.toReal + (y - C.toReal)))
      (X.ν.restrict (Iic (-1 : ℝ)))) :
    (∫ z in Iic (-1 : ℝ),
      (if y + z ≤ C.toReal then w (y + z)
       else w C.toReal + (y + z - C.toReal)) -
        (w C.toReal + (y - C.toReal)) ∂X.ν) ≤ 0 := by sorry
