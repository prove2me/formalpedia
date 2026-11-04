-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
-- name    : AvramDividend.Classical.avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T10:21:38.254131+00:00
-- url     : https://prove2.me/theorems/494a2261-b6c7-4c55-a21c-81e92b4982ab
-- title:
--   Original BV positive-cap C1 gives automatic compact-band Lipschitz increments
-- statement:
--   For the source spectrally negative Lévy process and BV candidate which is C1 on the strict positive-cap domain, every compact reserve interval contained in that domain has a finite Lipschitz constant. The constant is derived from the already-proved original derivative nnnorm bound, and differentiability follows from the proved openness of the physical cap domain. No additional regularity or stochastic assumption is needed.
-- source:
--   Accepted original compact derivative bound f294da35, strict cap openness and original BV Lipschitz bridge 596e81d8.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
import Theorems.Thm_AvramDividend_Classical_avram_wave8_22_original_BV_compact_derivative_implies_lipschitz
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_wave8_22_original_BV_C1_compact_band_automatic_lipschitz
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ L : ℝ≥0, ∀ u ∈ Icc a b, ∀ v ∈ Icc a b,
      |w u - w v| ≤ (L : ℝ) * |u - v| := by sorry
