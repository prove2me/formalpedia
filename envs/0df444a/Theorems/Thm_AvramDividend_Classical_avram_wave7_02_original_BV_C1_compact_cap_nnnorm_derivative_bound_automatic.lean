-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
-- name    : AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T00:04:17.78796+00:00
-- url     : https://prove2.me/theorems/f294da35-3b1e-4979-9576-19b7eff2ffd6
-- title:
--   Actual BV positive-cap C1 compact reserve strip admits an automatic nonnegative-real uniform derivative nnnorm bound
-- statement:
--   On the exact spectrally negative Lévy X and BV positive-cap candidate w, source C1 regularity makes the derivative bounded on each compact original reserve strip. The previously Proved automatic-open real derivative bound is transferred to a nonnegative-real derivative norm bound K. This removes the independent norm-bound hypothesis needed by the source C1 mean-value Lipschitz and finite-grid Stieltjes HJB lemmas; no new process or measure is introduced.
-- source:
--   Original source Proved 07ca388c compact |deriv| bound converted by real norm equals abs and nonnegative norm coercion; useful to W8-04's physical C1 stopped grid.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_wave7_02_original_BV_C1_compact_cap_derivative_bound_automatic_open
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_wave7_02_original_BV_C1_compact_cap_nnnorm_derivative_bound_automatic
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : X.BoundedVariation)
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC1 : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ≥0, ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K := by sorry
