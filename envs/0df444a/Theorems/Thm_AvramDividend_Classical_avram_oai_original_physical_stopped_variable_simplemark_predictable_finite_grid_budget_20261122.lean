-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_stopped_variable_simplemark_predictable_finite_grid_budget_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_stopped_variable_simplemark_predictable_finite_grid_budget_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:23:46.450819+00:00
-- url     : https://prove2.me/theorems/888b71ec-0ba5-4fa4-8f92-5818bd4ecfb9
-- title:
--   True original spectrally negative Lévy finite-grid compensated signed variable negative-mark process stopped by actual right-continuous stopping-time survival indicators has exact zero expected noise
-- statement:
--   For the ACTUAL original spectrally negative Lévy physical marked jump process (globally infinite activity allowed), any true right-continuous stopping time τ, and any finite collection of positive time-grid cells (s_i,t_i] with cell-specific locally finite negative Borel mark region S_i, real finite-range signed mark function g_i, and genuinely right-continuous-past-measurable stochastic weight H_i, form its survival-masked coefficient W_i=1_{τ>s_i}H_i. Under only per-cell integrability of W_i times the actual compensated signed marked-jump increment G_i, prove the entire stopped physical predictable marked-grid sum integrable with EXACT expectation zero. Source proof combines independently Proved original all-activity VARIABLE spatial-mark finite-grid signed compensated source theorem dd4edb76 and independently Proved true stopping-time survival mask filtration measurability 54d9e03e. This is the true stopped predictable jump first-moment source required in the original positive-clock Itô–Meyer budget. The nonlinear generator/Taylor remainder and Gaussian martingale remain open separate obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
import Theorems.Thm_AvramDividend_Classical_avram_oai_rightcont_stopping_mask_of_stronglyMeasurable_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_stopped_variable_simplemark_predictable_finite_grid_budget_20261122
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
    (∀ i ∈ F, Integrable (fun ω => W i ω * G i ω) P) →
      Integrable (fun ω => ∑ i ∈ F, W i ω * G i ω) P ∧
        (∫ ω, ∑ i ∈ F, W i ω * G i ω ∂P) = 0 := by sorry
