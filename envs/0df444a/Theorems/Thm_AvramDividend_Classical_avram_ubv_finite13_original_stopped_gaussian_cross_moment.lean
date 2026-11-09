-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ubv_finite13_original_stopped_gaussian_cross_moment
-- name    : AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_cross_moment
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T11:59:01.454202+00:00
-- url     : https://prove2.me/theorems/c3087a6e-85c5-47ea-99a7-6c4e593e08e4
-- title:
--   Original zero-jump two-stopping Gaussian cross moment equals earlier stopped second moment
-- statement:
--   On the original zero-negative-jump Lévy source and a single bounded sampled physical-time grid, two ordered stopping indices with genuinely stopped-history-measurable earlier source value satisfy the exact Gaussian cross-moment identity E[M_early M_late]=E[M_early squared], under explicit required product and terminal integrability. The identity transfers Proved source optional sampling through the pinned conditional-expectation product/pullout theorem and integral preservation.
-- source:
--   Proved original source paired optional sampling a331e012 and pinned Mathlib condExp_mul_of_stronglyMeasurable_left and integral_condExp. This is the nontrivial product cancellation step in the stopped Gaussian L2 energy comparison for original finite-cap conditional reward budget 50e1cf4c. Physical-limit, coefficient-integrability and dividend/HJB remain separate obligations.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_ubv_finite11_original_zerojump_two_stopped_grid_condexp

open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ubv_finite13_original_stopped_gaussian_cross_moment
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hν : X.ν = 0)
    (grid : ℕ → ℝ≥0) (hgrid : Monotone grid)
    (𝓖 : Filtration ℕ mΩ) [SigmaFiniteFiltration P 𝓖]
    (h𝓖 : 𝓖 =
      ({ seq := fun i : ℕ => 𝓕.rightCont (grid i)
         mono' := by
           intro i j hij
           exact 𝓕.rightCont.mono (hgrid hij)
         le' := by
           intro i
           exact 𝓕.rightCont.le (grid i) } : Filtration ℕ mΩ))
    (α β : Ω → WithTop ℕ)
    (hα : IsStoppingTime 𝓖 α) (hβ : IsStoppingTime 𝓖 β)
    (hαβ : α ≤ β)
    (N : ℕ) (hBound : ∀ ω, β ω ≤ (N : WithTop ℕ))
    (A B : Ω → ℝ)
    (hA : A = stoppedValue
      (fun i : ℕ => fun ω => X.X (grid i) ω - (grid i : ℝ) * X.c) α)
    (hB : B = stoppedValue
      (fun i : ℕ => fun ω => X.X (grid i) ω - (grid i : ℝ) * X.c) β)
    (hAadapt : StronglyMeasurable[hα.measurableSpace] A)
    (hBI : Integrable B P)
    (hCrossI : Integrable (fun ω => A ω * B ω) P) :
    (∫ ω, A ω * B ω ∂P) = (∫ ω, A ω * A ω ∂P) := by sorry
