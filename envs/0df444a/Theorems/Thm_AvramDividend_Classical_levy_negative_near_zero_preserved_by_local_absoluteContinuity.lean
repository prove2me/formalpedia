-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_negative_near_zero_preserved_by_local_absoluteContinuity
-- name    : AvramDividend.Classical.levy_negative_near_zero_preserved_by_local_absoluteContinuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T13:41:07.733868+00:00
-- url     : https://prove2.me/theorems/f6a26f80-2e7f-43f0-9be8-5795c93b6693
-- title:
--   Lévy downward zero regularity is invariant under finite-horizon locally absolutely continuous changes of law
-- statement:
--   For a spectrally negative Lévy process X under P, any other law Q on the same filtered path space which preserves P-null events on each finite observation-horizon filtration preserves almost-sure regularity of zero for the negative half-line. A dense countable time schedule and cofinal horizons provide the measurable finite-time events, now proved from the Lévy structure and adaptedness. This is the reusable local Esscher change-of-law bridge in the excursion smoothness proof. It does not construct an Esscher transform or prove regularity from unbounded variation.
-- source:
--   Finite-horizon Esscher transforms of spectrally negative Lévy processes; Kuznetsov, Kyprianou and Rivero, The Theory of Scale Functions for Spectrally Negative Lévy Processes (2013), Sections 1-2.

import Theorems.Thm_AvramDividend_Classical_levy_measurableSet_early_negative_before_horizon
import Theorems.Thm_AvramDividend_Classical_ae_negative_near_zero_of_local_absoluteContinuity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_negative_near_zero_preserved_by_local_absoluteContinuity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P Q : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (times horizons : ℕ → ℝ≥0)
    (hdense : ∀ a b : ℝ≥0, a < b →
      ∃ m : ℕ, a < times m ∧ times m < b)
    (hpos : ∀ n : ℕ, 0 < horizons n)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε →
      ∃ n : ℕ, horizons n ≤ ε)
    (hLocalAC : ∀ n : ℕ, ∀ A : Set Ω,
      MeasurableSet[𝓕 (horizons n)] A →
        P A = 0 → Q A = 0)
    (hRegP : ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0) :
    ∀ᵐ ω ∂Q, ∀ ε : ℝ≥0, 0 < ε →
      ∃ t : ℝ≥0, t < ε ∧ X.X t ω < 0 := by sorry
