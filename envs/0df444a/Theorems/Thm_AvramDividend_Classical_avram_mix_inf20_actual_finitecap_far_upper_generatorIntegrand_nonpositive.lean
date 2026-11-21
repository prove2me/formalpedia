-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_actual_finitecap_far_upper_generatorIntegrand_nonpositive
-- name    : AvramDividend.Classical.avram_mix_inf20_actual_finitecap_far_upper_generatorIntegrand_nonpositive
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:46:55.446212+00:00
-- url     : https://prove2.me/theorems/23aaef80-d457-43b2-b7bc-8a77ac1390f7
-- title:
--   Original infinite-activity Lévy above finite cap by one unit true truncated generator negative-mark integrand nonpositive for all negative jumps
-- statement:
--   Genuine original finite-cap spectrally negative Lévy far-above-barrier generator-integrand signed estimate, valid for all negative jump marks and actual original truncation indicator. For premark y≥C+1, every small negative jump with -1<z<0 remains strictly above cap, so caplinear V has exact zero compensated Taylor term. Every large negative jump z≤-1 has true uncompensated raw decrease V(y+z)-V(y)≤0 even if it ruins the reserve. Hence SpectrallyNegativeLevy.generatorIntegrand V y z≤0 for ALL negative z. Combine Proved literal truncation f6a26339, Proved above-strip zero-mark c82da644, and Proved all-negative raw potential 22675bab. This gives an integration-ready far-upper HJB dissipativity bound without requiring first moments of large negative marks or ruin-overshoot L1.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_actual_finitecap_far_upper_generatorIntegrand_nonpositive
    (C : ℝ≥0∞) (hC : 0 < C) (hFinite : C ≠ ⊤)
    (w : ℝ → ℝ) (hw0 : 0 ≤ w 0)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_neg : ∀ u : ℝ, u < 0 → w u = 0)
    (hw_smooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y)
    (y z : ℝ) (hy : C.toReal + 1 ≤ y) (hz : z < 0) :
    let V : ℝ → ℝ := fun t =>
      if t ≤ C.toReal then w t else w C.toReal + (t - C.toReal)
    SpectrallyNegativeLevy.generatorIntegrand V y z ≤ 0 := by sorry
