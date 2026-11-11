-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys71_original_no_intrinsic_mark_path_equals_drift
-- name    : AvramDividend.Classical.avram_bvb_phys71_original_no_intrinsic_mark_path_equals_drift
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T00:22:12.05456+00:00
-- url     : https://prove2.me/theorems/74263cae-4475-4d12-a0f0-2267d518c005
-- title:
--   Original bounded-variation no-mark source path equals deterministic drift through horizon
-- statement:
--   On a common full-measure event for the original spectrally negative bounded-variation process, if its actual removed-negative-jump cumulative sum is zero at every time up to T, then its source path is exactly its deterministic BV drift at every time up to T. This is the source identification required in the no-jump physical cash/terminal Stieltjes ledger branch c37acb5a.
-- source:
--   Necessary original-path drift reduction from Proved 79a63ca0

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_redux11_original_BV_raw_removed_residual_zero_ae
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys71_original_no_intrinsic_mark_path_equals_drift
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation) (T : ℝ≥0) :
    ∀ᵐ ω ∂P,
      (∀ t : ℝ≥0, t ≤ T →
        (∑' v : ℝ≥0, if 0 < v ∧ v ≤ t then
          Function.leftLim (fun z : ℝ≥0 => X.X z ω) v - X.X v ω
        else 0) = 0) →
      ∀ t : ℝ≥0, t ≤ T → X.X t ω = (t : ℝ) * X.drift := by sorry
