-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:25:31.573302+00:00
-- url     : https://prove2.me/theorems/c02b7b5c-8ec9-4781-838f-5042e3135da6
-- title:
--   Original finite BV simple predictable negative-jump rectangles have integrable centred real sum
-- statement:
--   For the unchanged original spectrally negative Levy source, an arbitrary finite family of adapted negative-mark rectangles and their explicit future-increment extractors has a compensated real-valued finite sum that is integrable with zero mean. Derived from the accepted W7-01 finite-simple positive Campbell identity by exact finite sum, ENNReal-to-real L1 conversion and real integral linearity. Explicit finite negative activity and source-measurability/localisation assumptions remain; this is an intermediate finite-simple martingale statement, not full stopped infinite-activity compensation.
-- source:
--   Accepted finite-simple predictable Campbell theorem 4c14ef8b-2a49-490c-81b2-714ec82ead03; finite sums of original negative-mark jump counts; exact original process Ω,P,𝓕,X; no assumed real zero-mean martingale property.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_01_bv_finite_simple_predictable_compensation_of_extractors
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (H : ℕ → Ω → ℝ≥0∞)
    (hH : ∀ i ∈ S, Measurable[𝓕 (s i)] (H i))
    (hHm : ∀ i ∈ S, Measurable (H i))
    (F : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞)
    (hF : ∀ i ∈ S, Measurable (F i))
    (N : ℕ → Ω → ℝ≥0∞)
    (hN : ∀ i ∈ S, ∀ ω : Ω, N i ω =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)))
    (hExtract : ∀ i ∈ S, ∀ ω : Ω,
      N i ω = F i (fun v : ℝ≥0 => X.X (s i + v) ω - X.X (s i) ω))
    (J K : Ω → ℝ≥0∞)
    (hJ : ∀ ω, J ω = ∑ i ∈ S, H i ω * N i ω)
    (hK : ∀ ω, K ω = ∑ i ∈ S, H i ω *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))))
    (hJm : AEMeasurable J P) (hKm : AEMeasurable K P)
    (hJae : ∀ᵐ ω ∂P, J ω < ⊤) (hKae : ∀ᵐ ω ∂P, K ω < ⊤)
    (hKfin : (∫⁻ ω, K ω ∂P) < ⊤) :
    Integrable (fun ω => (J ω).toReal - (K ω).toReal) P ∧
    (∫ ω, (J ω).toReal - (K ω).toReal ∂P) = 0 := by sorry
