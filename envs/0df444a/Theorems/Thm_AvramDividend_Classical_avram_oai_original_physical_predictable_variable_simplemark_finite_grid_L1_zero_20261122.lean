-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
-- name    : AvramDividend.Classical.avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-22T17:13:18.084348+00:00
-- url     : https://prove2.me/theorems/dd4edb76-98cb-4e79-80ce-ae5688184706
-- title:
--   True original physical Lévy compensated signed finite-grid martingale with changing Borel mark cells and distinct simple real jump integrands, all global jump activities
-- statement:
--   For the ACTUAL original spectrally negative Lévy physical marked jump process, any finite deterministic grid of time cells with cell-specific locally ν-finite negative Borel mark regions S_i and cell-specific signed real finite-range simple mark integrands g_i, and each random predictable weight H_i measurable in the ORIGINAL right-continuous filtration at the start s_i, let G_i be the fully physical compensated signed marked jump count over (s_i,t_i]. If H_i G_i is integrable in each finite cell, then their whole grid signed compensated sum is integrable and has EXACT zero expectation. Infinite overall negative jump activity is permitted; each cell can vary the spatial mark quantiser and region as needed for the spatial-time predictable jump-integrand approximation in stopped Ito–Meyer. Prove by independently remotely Proved true physical right-continuous conditional signed mark centring with H_i (d44667bc), original finite ν Borel marked process, pinned integral_condExp and finite integrable sum. Unlike simpler same-mark grid theorem 2874b7b7, this formulation supports different local mark approximations at every grid cell, a direct step toward the full state-dependent negative-jump Ito–Meyer witness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_oai_original_physical_simple_signed_mark_predictable_weight_condExp_zero_allactivity_20261122
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section
set_option autoImplicit false

theorem AvramDividend.Classical.avram_oai_original_physical_predictable_variable_simplemark_finite_grid_L1_zero_20261122
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
      StronglyMeasurable[𝓕.rightCont (s i)] (H i)) :
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
    (∀ i ∈ F, Integrable (fun ω => H i ω * G i ω) P) →
      Integrable (fun ω => ∑ i ∈ F, H i ω * G i ω) P ∧
        (∫ ω, ∑ i ∈ F, H i ω * G i ω ∂P) = 0 := by sorry
