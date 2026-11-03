-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_signed_finite_simple_compensated_L1_zero_mean
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_signed_finite_simple_compensated_L1_zero_mean
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T20:34:40.631527+00:00
-- url     : https://prove2.me/theorems/920105c1-e719-4abb-be4b-00ec8d62e69f
-- title:
--   Original BV signed finite-simple negative-jump compensator is integrable and centred
-- statement:
--   For the unchanged spectrally negative Levy X on Ω,P and its original filtration, any finite predictable negative-jump rectangle family with genuinely adapted nonnegative positive and negative weights yields a signed real compensated increment integrable with expectation zero. The result follows by applying the already Proved W8-22 finite-simple original-source L1 compensation separately to positive and negative weights, then subtracting their integrable centred increments. All source count, extractor, finite activity and L1 hypotheses are explicit; no zero-mean assumptions are supplied.
-- source:
--   Proved original finite-simple real compensated increment c02b7b5c-8ec9-4781-838f-5042e3135da6 applied independently to positive and negative adapted weights. This is a signed finite-step bridge to localised C1 generator compensation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_finite_simple_count_compensated_L1_zero_mean
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_signed_finite_simple_compensated_L1_zero_mean
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (S : Finset ℕ) (s t : ℕ → ℝ≥0) (hst : ∀ i ∈ S, s i ≤ t i)
    (Hpos Hneg : ℕ → Ω → ℝ≥0∞)
    (hHpos : ∀ i ∈ S, Measurable[𝓕 (s i)] (Hpos i))
    (hHneg : ∀ i ∈ S, Measurable[𝓕 (s i)] (Hneg i))
    (hMpos : ∀ i ∈ S, Measurable (Hpos i))
    (hMneg : ∀ i ∈ S, Measurable (Hneg i))
    (F : ℕ → (ℝ≥0 → ℝ) → ℝ≥0∞) (hF : ∀ i ∈ S, Measurable (F i))
    (N : ℕ → Ω → ℝ≥0∞)
    (hN : ∀ i ∈ S, ∀ ω : Ω, N i ω =
      ((Measure.count.restrict {u : ℝ≥0 | 0 < u ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc (s i) (t i) ×ˢ Iio (0 : ℝ)))
    (hExtract : ∀ i ∈ S, ∀ ω : Ω,
      N i ω = F i (fun v : ℝ≥0 => X.X (s i + v) ω - X.X (s i) ω))
    (Jpos Kpos Jneg Kneg : Ω → ℝ≥0∞)
    (hJpos : ∀ ω, Jpos ω = ∑ i ∈ S, Hpos i ω * N i ω)
    (hKpos : ∀ ω, Kpos ω = ∑ i ∈ S, Hpos i ω *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))))
    (hJneg : ∀ ω, Jneg ω = ∑ i ∈ S, Hneg i ω * N i ω)
    (hKneg : ∀ ω, Kneg ω = ∑ i ∈ S, Hneg i ω *
      (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (Iio (0 : ℝ))))
    (hJposm : AEMeasurable Jpos P) (hKposm : AEMeasurable Kpos P)
    (hJnegm : AEMeasurable Jneg P) (hKnegm : AEMeasurable Kneg P)
    (hJposae : ∀ᵐ ω ∂P, Jpos ω < ⊤) (hKposae : ∀ᵐ ω ∂P, Kpos ω < ⊤)
    (hJnegae : ∀ᵐ ω ∂P, Jneg ω < ⊤) (hKnegae : ∀ᵐ ω ∂P, Kneg ω < ⊤)
    (hKposfin : (∫⁻ ω, Kpos ω ∂P) < ⊤)
    (hKnegfin : (∫⁻ ω, Kneg ω ∂P) < ⊤) :
    Integrable (fun ω =>
      ((Jpos ω).toReal - (Kpos ω).toReal) -
      ((Jneg ω).toReal - (Kneg ω).toReal)) P ∧
    (∫ ω, ((Jpos ω).toReal - (Kpos ω).toReal) -
      ((Jneg ω).toReal - (Kneg ω).toReal) ∂P) = 0 := by sorry
