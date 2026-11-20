-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
-- name    : AvramDividend.Classical.avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T21:05:50.116644+00:00
-- url     : https://prove2.me/theorems/7c8c6812-2298-42eb-8679-7e5d53b44da8
-- title:
--   Original UBV HJB candidate global exponential bound from true scale-function first-exit comparison
-- statement:
--   Given the authentic original q-scale function W of a UBV spectrally negative Lévy and true killed first-exit comparison w(y)≤A W(y) at y≥1, along with genuine w continuous and w0≥0, prove global upper exponential growth of w through Proved original scale exp envelope and compact [0,1] bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
set_option autoImplicit false
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_UBV_HJB_scale_compare_implies_exponential_growth
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q) (w : ℝ → ℝ)
    (hw0 : 0 ≤ w 0) (hwcont : ContinuousOn w (Ici 0))
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (A : ℝ) (hA : 0 ≤ A)
    (hComp : ∀ y : ℝ, 1 ≤ y → w y ≤ A * W y) :
    ∃ θ K : ℝ, 0 ≤ θ ∧ 0 ≤ K ∧
      ∀ y : ℝ, 0 ≤ y → w y ≤ K * Real.exp (θ * y) := by sorry
