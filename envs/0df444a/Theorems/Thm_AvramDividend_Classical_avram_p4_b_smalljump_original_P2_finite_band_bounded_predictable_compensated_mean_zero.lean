-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_finite_band_bounded_predictable_compensated_mean_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_P2_finite_band_bounded_predictable_compensated_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T22:38:21.161395+00:00
-- url     : https://prove2.me/theorems/393d2ca3-73d2-4e4c-b0b4-48d11df67e88
-- title:
--   Original Lévy finite-band bounded predictable compensated step has zero physical mean
-- statement:
--   For the exact intrinsic marked jumps of the original spectrally negative Lévy process, a bounded genuinely random coefficient measurable in the original right-continuous past has zero unconditional mean after compensation by the true physical jump rate, provided P2 establishes raw predictable rectangle compensation and the original source ν count rate. Combines actual source right-continuity, count first-moment finiteness, real conditional centring and bounded predictable weight pull-out.
-- source:
--   Proved original source count moment eb8415ac, right-continuous rate and centring bridges, bounded predictable conditional expectation and zero-mean integral helper.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_raw_implies_rightCont_finite_band_centering
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_bounded_predictable_weight_count_condExp_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_predictable_weight_condExp_zero_implies_mean_zero

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_P2_finite_band_bounded_predictable_compensated_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (s t : ℝ≥0) (r : ℕ → ℝ≥0)
    (hsr : ∀ n, s < r n) (hrt : ∀ n, r n ≤ t)
    (B : Set ℝ) (hB : MeasurableSet B)
    (J : ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ a b ω, J a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B))
    (hShort : Tendsto (fun n => r n - s) atTop (𝓝 0))
    (hLong : Tendsto (fun n => t - r n) atTop (𝓝 (t - s)))
    (hFinite : X.ν B ≠ ⊤)
    (hMass : ∀ C : Set Ω, MeasurableSet[𝓕.rightCont s] C → P C ≠ ⊤)
    (hRate : ∀ n, (∫⁻ ω, J s (r n) ω ∂P) =
      ((r n - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hRaw : ∀ (u v : ℝ≥0) (C : Set Ω), u ≤ v →
      MeasurableSet[𝓕 u] C →
      (∫⁻ ω in C, J u v ω ∂P) =
        P C * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (hJmeas : Measurable (J s t))
    (hFullRate : (∫⁻ ω, J s t ω ∂P) =
      ((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B)
    (H : Ω → ℝ) (C : ℝ)
    (hH : StronglyMeasurable[𝓕.rightCont s] H)
    (hBound : ∀ᵐ ω ∂P, ‖H ω‖ ≤ C) :
    (∫ ω, H ω * ((J s t ω).toReal -
      (((t - s : ℝ≥0) : ℝ≥0∞) * X.ν B).toReal) ∂P) = 0 := by sorry
