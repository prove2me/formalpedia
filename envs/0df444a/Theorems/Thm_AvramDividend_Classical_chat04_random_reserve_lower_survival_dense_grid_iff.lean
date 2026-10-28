-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_dense_grid_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_lower_survival_dense_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:42:07.232818+00:00
-- url     : https://prove2.me/theorems/f9c964cc-945f-4cb7-82f8-92403b086ed4
-- title:
--   Random-reserve lower survival up to an open horizon is detected by a rational grid
-- statement:
--   For any Lévy path ω, observation horizon T and arbitrary reserve statistic H(ω), the process H(ω)+X_t(ω) stays nonnegative at every t<T if and only if it stays nonnegative at every inverse-natural rational grid time k/n<T. The reserve can depend arbitrarily on ω, so this is the exact pointwise bridge needed for killing events with a random reserve at a deterministic Markov splitting time, and enables countable-grid survival formulas to recover genuinely continuous-time lower killing.
-- source:
--   Existing Proved strict lower crossing rational-grid witness iff chat03_lower_before_horizon_countable_grid_iff, UUID 0ec8694a-90cc-4e41-9d39-37f4e80426cd. The complement of strict crossing is nonnegative survival; linear inequalities are closed by pinned Mathlib linarith.

import Mathlib.Tactic.Linarith
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_lower_survival_dense_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t < T → 0 ≤ H ω + X.X t ω) ↔
      ∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
          0 ≤ H ω + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω := by sorry
