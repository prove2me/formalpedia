-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_finitecap_real_interior_HJB_bridge
-- name    : AvramDividend.Classical.avram_ubv_loc6_finitecap_real_interior_HJB_bridge
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T00:16:43.6022+00:00
-- url     : https://prove2.me/theorems/a84cc060-8bc2-414a-a286-410ae19371b1
-- title:
--   Exact original finite-cap ENNReal interior HJB and C2 hypotheses as a real interval
-- statement:
--   Translate the actual original finite ENNReal cap interior into the open real interval (0, C.toReal), transporting all the original C2 smoothness, generator integrability/HJB and dividend derivative lower-bound hypotheses needed to instantiate compact stopped Ito–Meyer source estimates.
-- source:
--   Source-exact conversion at the original finite C ≠ top using the pinned ENNReal.ofReal_lt_iff_lt_toReal equivalence on strictly positive reserve values; no boundedness or smoothness at zero or cap endpoints is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_ubv_loc6_finitecap_real_interior_HJB_bridge
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (w : ℝ → ℝ) (C : ℝ≥0∞)
    (hC : 0 < C) (hFinite : C ≠ ⊤)
    (hw_smooth : ContDiffOn ℝ 2 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (q : ℝ)
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ContDiffOn ℝ 2 w (Ioo 0 C.toReal) ∧
    (∀ y : ℝ, 0 < y → y < C.toReal →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0) ∧
    (∀ y : ℝ, 0 < y → y < C.toReal → 1 ≤ deriv w y) := by sorry
