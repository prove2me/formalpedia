-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian13_actual_masked_random_interval_square_integrable
-- name    : AvramDividend.Classical.avram_ubv_gaussian13_actual_masked_random_interval_square_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T13:29:43.526967+00:00
-- url     : https://prove2.me/theorems/382a45a1-7e20-43a5-88ec-123b786979a2
-- title:
--   Actual masked Gaussian square energy integrable between any finite-mass random endpoints
-- statement:
--   For the actual original Lévy source and unchanged right-continuous filtration, the compact-masked Gaussian derivative has integrable squared energy on every sample-dependent interval of finite physical time-measure mass. Predictability provides time-section measurability and compact C² smoothness bounds the coefficient. No adaptation of the process or filtration is introduced.
-- source:
--   Proved 7ae1130d predictable original masked gradient, cd58d62b original time sections, 9645ebf8 compact derivative cap; integrates arbitrary random-clock increments to support stopped L² stochastic integrals.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_loc6_original_gaussian_masked_gradient_source_L2
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_masked_gaussian_uniform_bound
import Theorems.Thm_AvramDividend_Classical_avram_ubv_gaussian10_original_predictable_time_section_measurable

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gaussian13_actual_masked_random_interval_square_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (w : ℝ → ℝ) (a b u v : ℝ)
    (hw : ContDiffOn ℝ 2 w (Ioo a b))
    (hau : a < u) (huv : u ≤ v) (hvb : v < b)
    (μ : @Measure (ℝ≥0 × Ω) (𝓕.rightCont.predictable))
    (hμ : μ Set.univ < ⊤)
    (μtime : Measure ℝ≥0) (s t : Ω → ℝ≥0)
    (hFinite : ∀ ω, μtime (Ioc (s ω) (t ω)) < ⊤) :
    let Y : ℝ≥0 × Ω → ℝ := fun p => Function.leftLim
      (fun r : ℝ≥0 => x + X.X r p.2 - rightLimit D r p.2) p.1
    let H : ℝ≥0 × Ω → ℝ := fun p =>
      if Y p ∈ Icc u v then deriv w (Y p) else 0
    let G : ℝ≥0 × Ω → ℝ := fun p => X.σ * H p
    ∀ ω, IntegrableOn (fun r : ℝ≥0 => (G (r, ω)) ^ 2)
      (Ioc (s ω) (t ω)) μtime := by sorry
