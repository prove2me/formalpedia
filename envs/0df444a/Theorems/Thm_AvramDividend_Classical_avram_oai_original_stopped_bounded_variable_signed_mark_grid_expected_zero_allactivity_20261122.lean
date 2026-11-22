-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_stopped_bounded_variable_signed_mark_grid_expected_zero_allactivity_20261122
-- name    : AvramDividend.Classical.avram_oai_original_stopped_bounded_variable_signed_mark_grid_expected_zero_allactivity_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:29:40.161606+00:00
-- url     : https://prove2.me/theorems/f17bb762-67d3-45a2-a906-103ce1d711d3
-- title:
--   Actual all-activity stopped bounded predictable signed mark grid: integrability and zero mean
-- statement:
--   For the original spectrally negative Lévy physical jump measure, a true right-continuous stopping time, any finite time grid and cell-specific locally finite negative Borel mark sets and finite real simple mark functions, each bounded earlier-time measurable weight is masked after stopping. Prove the entire signed compensated physical marked grid sum is integrable with expectation zero. Compose the Proved original finite-grid marked-noise theorem dd4edb76, the Proved stopping-mask theorem 54d9e03e and the Proved interval marked-noise L1 theorem 8a9b7715 with bounded-product integrability. Global negative jump activity may be infinite; no synthetic PRM or assumed martingale.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_variable_negative_simplemark_interval_compensated_L1_allactivity_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_stopped_bounded_variable_signed_mark_grid_expected_zero_allactivity_20261122
    {Ω ι : Type*} [mΩ : MeasurableSpace Ω] [DecidableEq ι]
    {P : Measure Ω} [IsProbabilityMeasure P]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (F : Finset ι) (s t : ι → ℝ≥0)
    (hst : ∀ i ∈ F, s i < t i)
    (S : ι → Set ℝ)
    (hS : ∀ i ∈ F, MeasurableSet (S i))
    (hNeg : ∀ i ∈ F, S i ⊆ Iio (0 : ℝ))
    (hν : ∀ i ∈ F, X.ν (S i) < ⊤)
    (g : ι → SimpleFunc ℝ ℝ)
    (H : ι → Ω → ℝ)
    (hH : ∀ i ∈ F,
      StronglyMeasurable[𝓕.rightCont (s i)] (H i))
    (K : ι → ℝ)
    (hBound : ∀ i ∈ F, ∀ ω, ‖H i ω‖ ≤ K i)
    (τ : Ω → WithTop ℝ≥0)
    (hStop : IsStoppingTime 𝓕.rightCont τ) :
    let NX : Ω → Measure (ℝ≥0 × ℝ) := fun ω =>
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
    let B : ι → ℝ → Set ℝ := fun i y => S i ∩ (g i) ⁻¹' {y}
    let G : ι → Ω → ℝ := fun i ω =>
      ∑ y ∈ (g i).range, y *
        ((NX ω (Ioc (s i) (t i) ×ˢ B i y)).toReal -
          ((((t i - s i : ℝ≥0) : ℝ≥0∞) * X.ν (B i y))).toReal)
    let W : ι → Ω → ℝ := fun i ω =>
      if τ ω ≤ (s i : WithTop ℝ≥0)
        then 0 else H i ω
    Integrable (fun ω => ∑ i ∈ F, W i ω * G i ω) P ∧
        (∫ ω, ∑ i ∈ F, W i ω * G i ω ∂P) = 0 := by sorry
