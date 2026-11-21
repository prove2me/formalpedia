-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_inf20_original_spectrally_negative_actual_generatorIntegrand_upperstrip_ruin_bound
-- name    : AvramDividend.Classical.avram_mix_inf20_original_spectrally_negative_actual_generatorIntegrand_upperstrip_ruin_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:34:35.571034+00:00
-- url     : https://prove2.me/theorems/8899fcd5-e543-4040-8dea-7c134ce593b9
-- title:
--   Exact original spectrally negative Lévy generatorIntegrand above finite cap bounded by ruin overshoot under true small/large truncation
-- statement:
--   Source-exact upper-strip original spectrally negative Lévy generator integrand, with exactly the definition SpectrallyNegativeLevy.generatorIntegrand and its literal small negative mark correction indicator 1_{(-1,1)}(z). For all negative z and premark y above finite cap, the corrected caplinear candidate V has generator mark ≤ positive ruin overshoot, including unrestricted large marks z≤-1 where no linear compensation is permitted. Combine server-Proved f6a26339 exact small/large truncation split, Proved finite-cap corrected complete small-mark estimate, and Proved raw large-negative-mark potential decrease, avoiding the unsound fullmark linear subtraction on large jumps. This deterministic result is ready for genuine original generator L1 integration and the five signed original stopped Itô-Meyer ledger.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_mix_inf20_original_spectrally_negative_actual_generatorIntegrand_upperstrip_ruin_bound
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
    SpectrallyNegativeLevy.generatorIntegrand V y z ≤ max 0 (-(y + z)) := by sorry
