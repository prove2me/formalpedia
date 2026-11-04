-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_finite_marked_truncation_eventual_weighted_sum
-- name    : AvramDividend.Classical.avram_wave7_06_original_finite_marked_truncation_eventual_weighted_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:13:53.70591+00:00
-- url     : https://prove2.me/theorems/38c589f2-ff2b-47a2-abbf-55cb03d8e9a5
-- title:
--   Actual finite marked source-jump truncations eventually preserve the weighted jump sum
-- statement:
--   For the exact finite set F of actual original separated-band marked jump times, take finite truncations G n included in F, such that each genuine source time is eventually included. Then the full original weighted jump sum agrees with each sufficiently advanced truncation, pointwise in the original sample path. The arbitrary real weight can be the stopped Taylor integrand on that path. No auxiliary point process or probabilistic equality is used, and no claim of uniform integrability is made.
-- source:
--   Finite intersection of eventual membership facts over original marked times.

import Mathlib
open Filter
open scoped NNReal

theorem AvramDividend.Classical.avram_wave7_06_original_finite_marked_truncation_eventual_weighted_sum
    (F : Finset ℝ≥0) (G : ℕ → Finset ℝ≥0) (H : ℝ≥0 → ℝ)
    (hSub : ∀ n, G n ⊆ F)
    (hEach : ∀ u ∈ F, ∀ᶠ n in Filter.atTop, u ∈ G n) :
    ∀ᶠ n in Filter.atTop,
      (∑ u ∈ G n, H u) = ∑ u ∈ F, H u := by sorry
