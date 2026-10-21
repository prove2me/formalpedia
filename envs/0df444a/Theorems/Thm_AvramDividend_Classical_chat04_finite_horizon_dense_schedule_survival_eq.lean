-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_finite_horizon_dense_schedule_survival_eq
-- name    : AvramDividend.Classical.chat04_finite_horizon_dense_schedule_survival_eq
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:08:34.241961+00:00
-- url     : https://prove2.me/theorems/55a4c9bb-55c9-4ea9-af90-93c4d35bcc4e
-- title:
--   Finite-horizon strict survival equals all dense-grid no-exit observations before T
-- statement:
--   For every spectrally negative Lévy process and finite horizon T, a countable deterministic observation schedule τ that covers all reciprocal-natural-grid times detects exactly whether the sample path avoids strict lower/upper exits at all times t<T. The continuous-time survival event up to the OPEN horizon is the intersection of no-exit events for those observations τ(j)<T. Uses independently Proved finite-horizon lower- and upper-crossing grid-density equivalences and explicit schedule coverage, and respects the strict t<T endpoint. This is the correct event-theoretic input for fixed-horizon killed Markov semigroups, unlike unrestricted lifetime survival.
-- source:
--   Proved AvramDividend.Classical.chat03_lower_before_horizon_countable_grid_iff UUID 0ec8694a-90cc-4e41-9d39-37f4e80426cd and chat03_upper_before_horizon_countable_grid_iff UUID c4e268ac-950c-4843-96a7-7742108a50c5.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat03_lower_before_horizon_countable_grid_iff
import Theorems.Thm_AvramDividend_Classical_chat03_upper_before_horizon_countable_grid_iff

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_finite_horizon_dense_schedule_survival_eq
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    {ω | ∀ t : ℝ≥0, t < T →
      ¬ (X.X t ω < lower ∨ upper < X.X t ω)} =
      ⋂ j : ℕ, {ω | τ j < T →
        ¬ (X.X (τ j) ω < lower ∨ upper < X.X (τ j) ω)} := by sorry
