-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_actual_truncated_generator_mark_overshoot
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_actual_truncated_generator_mark_overshoot
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T16:28:33.132379+00:00
-- url     : https://prove2.me/theorems/73db20db-8803-4efd-8d20-559833196782
-- title:
--   Genuine original negative Lévy generator-integrand with correct unit truncation bounded by small-mark ruin overshoot
-- statement:
--   Actual original spectrally negative Levy generatorIntegrand for finite cap, including its exact truncation z 1_{-1<z<1}. For any negative mark z, premark reserve y>C and corrected caplinear V: if z>-1, the compensated Taylor remainder is bounded above by the true positive ruin overshoot max(0,-(y+z)), using server-Proved full mark envelope 85b04ac6. If z≤-1, the generator has NO derivative subtraction and the raw marked difference V(y+z)-V(y) is nonpositive by server-Proved 22675bab. This fixes the heavy-tail shortcoming of fully compensated whole-line subtraction and is source-faithful to original SpectrallyNegativeLevy.generatorIntegrand. The only possible positive jump-generator cost lies in the bounded small-mark ruin-overshoot kernel. Its integration and stopping still need separate true L1/compensator checks.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_complete_mark_overshoot_envelope
import Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_all_negative_raw_marks_nonpos
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_actual_truncated_generator_mark_overshoot
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal < y) (hz : z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    SpectrallyNegativeLevy.generatorIntegrand V y z ≤
      if -1 < z then max 0 (-(y + z)) else 0 := by sorry
