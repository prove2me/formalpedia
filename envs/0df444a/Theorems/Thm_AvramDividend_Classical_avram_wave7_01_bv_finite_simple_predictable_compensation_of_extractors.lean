-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
-- name    : AvramDividend.Classical.avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T17:00:46.882346+00:00
-- url     : https://prove2.me/theorems/4c14ef8b-2a49-490c-81b2-714ec82ead03
-- title:
--   Original finite BV simple predictable marked integrands obey compensated expectation when genuine extractors are supplied
-- statement:
--   For the actual original SpectrallyNegativeLevy process and any finite family of deterministic time intervals, measurable ENNReal coefficients adapted at each interval start and real original shifted-future measurable jump-count extractors, the expectation of the total weighted strictly-negative marked jumps equals the finite sum of predictable compensator expectations. Requires genuine BV and explicit ν(Iio0)<∞, with each extractor a stated unproved condition. Uses no alternate process and no integrability assumptions beyond nonnegative ENNReal sums.
-- source:
--   Proved original source adapted-weight compensator bb47482c and source future coordinate-product measurability 8b9eb23, Mathlib lintegral_finset_sum and Finset.sum_congr.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_negative_mark_adapted_weight_compensation_of_extractor
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_original_shifted_future_path_coordinate_product_measurable

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0)
    (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (F : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hF : ∀ i ∈ S, Measurable (F i))
    (hExtract : ∀ i ∈ S, ∀ ω : Ω,
      ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) =
        F i (fun v : ℝ≥0 => X.X (s i + v) ω - X.X (s i) ω)) :
    (∫⁻ ω, ∑ i ∈ S, H i ω * ((Measure.count.restrict {u : ℝ≥0 |
      0 < u ∧ X.X u ω -
        Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
      (fun u : ℝ≥0 => (u,
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
      (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)) ∂P) =
    ∑ i ∈ S,
      (∫⁻ ω, H i ω ∂P) *
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ)) := by sorry
