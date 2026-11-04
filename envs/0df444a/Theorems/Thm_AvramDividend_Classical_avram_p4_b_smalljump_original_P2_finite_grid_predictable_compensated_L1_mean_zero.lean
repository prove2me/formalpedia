-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_finite_grid_predictable_compensated_L1_mean_zero
-- name    : AvramDividend.Classical.avram_p4_b_smalljump_original_P2_finite_grid_predictable_compensated_L1_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:02:04.48442+00:00
-- url     : https://prove2.me/theorems/1868c36c-ad4c-41b7-ab9c-74ed7089c657
-- title:
--   Original Levy P2 rates imply finite-grid bounded predictable compensated L1 zero mean
-- statement:
--   On the true original spectrally negative Levy process, raw P2 predictable marked count rates imply a finite sum of compensated finite-band marked jump counts with random bounded coefficients from each original right-continuous past has physical mean zero.
-- source:
--   Direct application of accepted original finite-band P2 bounded predictable compensation per cell plus count-moment integrability and finite Bochner-integral linearity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_P2_finite_band_bounded_predictable_compensated_mean_zero
import Theorems.Thm_AvramDividend_Classical_avram_p4_b_smalljump_original_finite_intensity_count_integrable_and_ae_finite

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p4_b_smalljump_original_P2_finite_grid_predictable_compensated_L1_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    {ι : Type*} (S : Finset ι)
    (s t : ι → ℝ≥0) (r : ι → ℕ → ℝ≥0)
    (hsr : ∀ i ∈ S, ∀ n, s i < r i n)
    (hrt : ∀ i ∈ S, ∀ n, r i n ≤ t i)
    (B : ι → Set ℝ) (hB : ∀ i ∈ S, MeasurableSet (B i))
    (J : ι → ℝ≥0 → ℝ≥0 → Ω → ℝ≥0∞)
    (hJsource : ∀ i a b ω, J i a b ω =
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
       (fun u : ℝ≥0 => (u,
          X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
       (Ioc a b ×ˢ B i))
    (hShort : ∀ i ∈ S,
      Tendsto (fun n => r i n - s i) atTop (𝓝 0))
    (hLong : ∀ i ∈ S,
      Tendsto (fun n => t i - r i n) atTop (𝓝 (t i - s i)))
    (hFinite : ∀ i ∈ S, X.ν (B i) ≠ ⊤)
    (hMass : ∀ i ∈ S, ∀ A : Set Ω,
      MeasurableSet[𝓕.rightCont (s i)] A → P A ≠ ⊤)
    (hRate : ∀ i ∈ S, ∀ n, (∫⁻ ω, J i (s i) (r i n) ω ∂P) =
      ((r i n - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (hRaw : ∀ i ∈ S, ∀ (u v : ℝ≥0) (A : Set Ω), u ≤ v →
      MeasurableSet[𝓕 u] A →
      (∫⁻ ω in A, J i u v ω ∂P) =
        P A * ((v - u : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (hJmeas : ∀ i ∈ S, Measurable (J i (s i) (t i)))
    (hFullRate : ∀ i ∈ S,
      (∫⁻ ω, J i (s i) (t i) ω ∂P) =
        ((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i))
    (H : ι → Ω → ℝ) (C : ι → ℝ)
    (hH : ∀ i ∈ S,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (hBound : ∀ i ∈ S, ∀ᵐ ω ∂P, ‖H i ω‖ ≤ C i) :
    (∫ ω, ∑ i ∈ S, H i ω *
      ((J i (s i) (t i) ω).toReal -
        (((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i)).toReal) ∂P) = 0 := by sorry
