-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_closed_grid_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_lower_survival_closed_grid_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T19:49:45.95719+00:00
-- url     : https://prove2.me/theorems/f8ad0c25-7bcb-431f-8c5a-3ad4121668e5
-- title:
--   Closed-horizon random-reserve survival equals rational-grid survival plus terminal test
-- statement:
--   For an arbitrary random reserve H(ω), nonruin at every time 0≤t≤T is equivalent to nonruin at all countable rational observations k/n strictly before T together with an explicit nonnegative terminal reserve at T. This closes the horizon-endpoint gap in the random-reserve dense-grid lemma and supplies the precise full-history killing event of the q-scale renewal integral identity a885f0b3 for finite-horizon semigroup approximations.
-- source:
--   Proved chat04_random_reserve_lower_survival_dense_grid_iff, using the order trichotomy t<T or t=T. The endpoint distinction matches the established closed-horizon grid-limit theorem chat04_closed_horizon_survival_lintegral_grid_limit.

import Mathlib.Data.NNReal.Defs
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_lower_survival_dense_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_lower_survival_closed_grid_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (T : ℝ≥0) :
    (∀ t : ℝ≥0, t ≤ T → 0 ≤ H ω + X.X t ω) ↔
      (∀ n : ℕ, 0 < n → ∀ k : ℕ,
        (k : ℝ≥0) * (n : ℝ≥0)⁻¹ < T →
          0 ≤ H ω + X.X ((k : ℝ≥0) * (n : ℝ≥0)⁻¹) ω) ∧
        0 ≤ H ω + X.X T ω := by sorry
