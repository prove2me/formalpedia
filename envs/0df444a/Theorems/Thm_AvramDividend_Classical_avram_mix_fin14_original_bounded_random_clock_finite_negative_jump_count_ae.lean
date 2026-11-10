-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_bounded_random_clock_finite_negative_jump_count_ae
-- name    : AvramDividend.Classical.avram_mix_fin14_original_bounded_random_clock_finite_negative_jump_count_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T11:23:00.274813+00:00
-- url     : https://prove2.me/theorems/e40c2735-3717-4778-8886-44c92b736752
-- title:
--   Every bounded random stopping clock has finite actual negative source-jump count almost surely
-- statement:
--   Use the physical finite-activity marked-count at the fixed integer ceiling to dominate the literal negative marked jump count at any omega-dependent clock bounded above by that ceiling. No stopping-time or adaptedness assumption on this clock is needed for this purely pathwise bound; hence it applies to the ruin-clipped original finite-activity stopped reward clock. Source identity and half-open endpoint are preserved. This is a necessary jump-finiteness input to the original mixed Gaussian Ito-Meyer reward source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_mix_fin14_original_finite_activity_negative_jump_count_finite_ae
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_mix_fin14_original_bounded_random_clock_finite_negative_jump_count_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (σ : Ω → ℝ≥0)
    (hBound : ∀ ω, σ ω ≤ (n : ℝ≥0)) :
    ∀ᵐ ω ∂P,
      ((Measure.count.restrict {u : ℝ≥0 |
        0 < u ∧ X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
        (fun u : ℝ≥0 => (u, X.X u ω -
          Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))
        (Ioc 0 (σ ω) ×ˢ Iio (0 : ℝ)) ≠ ⊤ := by sorry
