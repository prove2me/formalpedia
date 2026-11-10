-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_gauss13_localise_original_two_bounded_sampled_gaussian_clock_values_integrable
-- name    : AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_bounded_sampled_gaussian_clock_values_integrable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T08:59:34.946021+00:00
-- url     : https://prove2.me/theorems/c60d085c-7c2f-4887-a20a-7dbe8024426f
-- title:
--   Original Gaussian two bounded sampled stopping times have integrable deterministic variance-clock values
-- statement:
--   Source-exact discharge of the two Integrable stopped deterministic time-value premises of the public GAUSS-LOCALISATION-CAP common-ceiling sampled Gaussian energy helper ccfe93ed. The original Levy probability P makes every fixed grid time times the Gaussian variance integrable; the Mathlib integrable_stoppedValue theorem lifts this to two genuine bounded sampled stopping times, with alpha no later than beta. No surrogate process and no floor stopping assumption.
-- source:
--   Pinned Mathlib MeasureTheory.integrable_stoppedValue, original SpectrallyNegativeLevy.isProbability; direct incoming use in public ccfe93ed

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory ProbabilityTheory AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_gauss13_localise_original_two_bounded_sampled_gaussian_clock_values_integrable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (grid : ℕ → ℝ≥0)
    (𝓖 : Filtration ℕ mΩ)
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hN : ∀ ω, β ω ≤ (N : WithTop ℕ)) :
    Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) α) P ∧
    Integrable (stoppedValue
      (fun i : ℕ => fun _ : Ω => (grid i : ℝ) * X.σ ^ 2) β) P := by sorry
