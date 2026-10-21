-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_strict_survival_measurable
-- name    : AvramDividend.Classical.chat04_closed_horizon_strict_survival_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-20T10:23:08.862772+00:00
-- url     : https://prove2.me/theorems/55b18d50-b036-42df-a6c0-256d10161e75
-- title:
--   Continuous-time finite-horizon two-barrier survival event is measurable
-- statement:
--   For any canonical spectrally negative Lévy process, finite horizon T, strict lower/upper barriers and a countable observation schedule containing every reciprocal-natural-grid time, the event of no strict barrier crossing at any continuous time t≤T is measurable in the original sample-space sigma-algebra. The original event has an uncountable universal quantifier; prove measurability using the ACCEPTED exact closed-horizon dense-grid survival identity, countable measurable intersections of adapted Lévy observations and the separate terminal-time check. This is a genuine stochastic measurability prerequisite for killed-process conditional expectations, requiring no q-scale martingale or zero-probability fixed-time jump argument.
-- source:
--   Accepted chat04_closed_horizon_dense_survival_eq UUID 857f5ba3-a81a-43ee-9027-9dae04e67e45 and canonical SpectrallyNegativeLevy.adapted.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_chat04_closed_horizon_dense_survival_eq

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_closed_horizon_strict_survival_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (lower upper : ℝ) (T : ℝ≥0) :
    MeasurableSet
      {ω | ∀ t : ℝ≥0, t ≤ T →
        ¬ (X.X t ω < lower ∨ upper < X.X t ω)} := by sorry
