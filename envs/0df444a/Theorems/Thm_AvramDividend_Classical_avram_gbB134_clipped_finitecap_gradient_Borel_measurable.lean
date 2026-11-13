-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB134_clipped_finitecap_gradient_Borel_measurable
-- name    : AvramDividend.Classical.avram_gbB134_clipped_finitecap_gradient_Borel_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T08:12:32.177581+00:00
-- url     : https://prove2.me/theorems/e0e8b49b-d8f5-4b14-b1bb-f58e8cc79384
-- title:
--   Borel measurability of clipped derivative in the original finite-cap band
-- statement:
--   The closed clipping band is strictly inside the positive finite-cap interior. The second-order ContDiffOn assumption yields continuous derivative on this band, hence the function equal to deriv w on the band and equal to one elsewhere is Borel measurable. This is the deterministic spatial measurability needed for the original jointly measurable physical clipped gradient.
-- source:
--   Proved B59 continuity-of-derivative on compact interior band proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB134_clipped_finitecap_gradient_Borel_measurable
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C) (hFiniteCap : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (δ : ℝ) (hδ : 0 < δ) (j : ℕ) :
    Measurable (fun y : ℝ =>
      let a : ℝ := δ / 2
      let b : ℝ := C.toReal * (((j + 1 : ℕ) : ℝ) / ((j + 2 : ℕ) : ℝ))
      if y ∈ Icc a b then deriv w y else 1) := by sorry
