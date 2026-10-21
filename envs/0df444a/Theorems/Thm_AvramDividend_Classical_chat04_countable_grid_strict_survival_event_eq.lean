-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_countable_grid_strict_survival_event_eq
-- name    : AvramDividend.Classical.chat04_countable_grid_strict_survival_event_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T07:41:06.936617+00:00
-- url     : https://prove2.me/theorems/2d1d4d5d-72ab-4e14-aedc-4018903df231
-- title:
--   Any countable schedule covering reciprocal natural grids detects exact continuous strict survival
-- statement:
--   For any canonical spectrally negative Lévy process X and real lower/upper boundaries, take a countable deterministic observation sequence τ:ℕ→ℝ≥0 which covers every rational time k/n for all n>0 and k≥0. Prove the set of sample paths that never exit the strict interval at any continuous time t≥0 is exactly the intersection over j of the no-strict-exit events sampled at τ_j. This is pathwise equality, not merely a.e.: the already accepted Chat03 theorem states every strict crossing of either boundary is detected by some k/n, and coverage gives an index j. No q-scale, integrability, local Lean or optional stopping is involved. This provides the precise countable-event identification needed to apply the decreasing grid survival-lintegral limit theorem, after constructing a suitable enumeration schedule.
-- source:
--   Proved AvramDividend.Classical.chat03_countable_inverse_nat_grid_exit_iff UUID ac8b9e52-5815-4817-aff2-65753a595d1f; elementary set extensionality and finite/countable grid inclusion.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_countable_inverse_nat_grid_exit_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_countable_grid_strict_survival_event_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) :
    {ω | ∀ t : ℝ≥0, ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      ⋂ j : ℕ,
        {ω | ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} := by sorry
