-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_phys37_original_single_negative_mark_predictable_weight_compensation
-- name    : AvramDividend.Classical.avram_bvb_phys37_original_single_negative_mark_predictable_weight_compensation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-10T12:24:01.593138+00:00
-- url     : https://prove2.me/theorems/edac779d-67f6-4f0a-951a-b9484063be8d
-- title:
--   Original finite-activity single negative-mark predictable-weight compensation without an extractor premise
-- statement:
--   In the original spectral-negative BV Levy process, finite negative jump intensity and the already proved future-mark extractor automatically discharge the extractor premise of the original predictable weighted count formula. For every deterministic s≤t and nonnegative original-filtration s-measurable H, expected weighted negative jump count equals expected H times interval length and original negative Levy rate. This is a genuine simple-kernel component of the stopped full-mark M_n centring proof; no auxiliary process or first jump-size moment.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb_phys37_original_single_negative_mark_predictable_weight_compensation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ≥0∞) (hH : Measurable[𝓕 s] H) :
    (∫⁻ ω, H ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc s t ×ˢ Iio (0 : ℝ)) ∂P) =
    (∫⁻ ω, H ω ∂P) *
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
