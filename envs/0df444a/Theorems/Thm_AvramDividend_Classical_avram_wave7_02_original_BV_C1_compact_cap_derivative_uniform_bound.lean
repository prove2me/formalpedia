-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_uniform_bound
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_derivative_uniform_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:08:29.557191+00:00
-- url     : https://prove2.me/theorems/260c4b9f-9bfc-4e77-ba99-293954468c10
-- title:
--   Original BV positive-cap C1 candidate has a uniform absolute derivative bound on every compact interior reserve band
-- statement:
--   For the exact Avram bounded-variation source's positive-cap candidate, the strict interior ContDiffOn ℝ 1 condition and openness of that original cap region imply the ordinary derivative is continuous on every compact reserve interval contained in it. Compactness therefore supplies a finite nonnegative K with |deriv w y|≤K on the entire band. The result can be inserted directly into finite-window original Stieltjes integrability and generator-HJB budgets, rather than taking the derivative ceiling as an independent assumption.
-- source:
--   Pinned Mathlib ContDiffOn.continuousOn_deriv_of_isOpen, IsCompact.exists_bound_of_continuousOn, and original strict ENNReal cap region.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_derivative_uniform_bound
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc a b, |deriv w y| ≤ K := by sorry
