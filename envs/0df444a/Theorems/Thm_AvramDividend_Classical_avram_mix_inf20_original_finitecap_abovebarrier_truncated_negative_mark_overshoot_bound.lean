-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
-- name    : AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:30:57.546447+00:00
-- url     : https://prove2.me/theorems/04efc17f-d06b-407c-9b59-8c50640a1d5c
-- title:
--   Genuine original finitecap truncated Lévy negative-mark Taylor generator bound by ruin overshoot
-- statement:
--   Source-faithful finite-cap above-barrier marked Lévy generator sign under the actual truncated negative-jump compensation χ(z)=z if -1<z<0, else 0. For every negative mark z, the exact caplinear V generator integrand V(y+z)-V(y)-V'(y)χ(z) is bounded by positive-part ruin overshoot max(0,-(y+z)). Small marks follow the proved active and ruin overshoot Taylor bounds; large marks use the separately Proved raw negative mark decrease. This respects full Lévy generator truncation and avoids the false full-mark z compensation on large jumps without a first moment. Actual expectation/integrability of overshoot must be established separately when integrating.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_finitecap_abovebarrier_truncated_negative_mark_overshoot_bound
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
    V (y + z) - V y -
      deriv V y * (if -1 < z then z else 0) ≤ max 0 (-(y + z)) := by sorry
