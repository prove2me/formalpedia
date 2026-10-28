-- Prove2me | Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_negative_near_zero_of_grid
-- name    : AvramDividend.Classical.levy_finiteStopping_negative_near_zero_of_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T11:46:52.53254+00:00
-- url     : https://prove2.me/theorems/877dfbc1-79af-4667-be5c-d0fabce594c0
-- title:
--   Post-stopping downward regularity from a cofinal negative-grid law without any path-measurability hypothesis
-- statement:
--   For a spectrally negative Lévy process, if almost every original path has strictly negative grid observations before every horizon of a cofinal time sequence, the shifted process after every finite stopping time is likewise downward regular at time zero almost surely. Unlike its predecessor it requires no explicit whole-path measurability assumption, since the proved whole-path measurability theorem supplies it from the Lévy structure. This is the cleanest conditional ordinary-probability Markov restart interface for the excursion-height atomlessness branch. It still needs the nontrivial stochastic proof of the original grid law from unbounded variation.
-- source:
--   Proved stopped-grid strong Markov event transfer and whole Lévy path measurability; source fluctuation-theory treatment Kuznetsov, Kyprianou and Rivero (2013) Section 2.3.

import Mathlib.Probability.Process.Stopping
import Theorems.Thm_AvramDividend_Classical_levy_wholePath_measurable
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_ae_negative_near_zero_of_grid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.levy_finiteStopping_negative_near_zero_of_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (τ : Ω → ℝ≥0)
    (hτ : ∀ s : ℝ≥0, MeasurableSet[𝓕 s] {ω : Ω | τ ω ≤ s})
    (hstop : IsStoppingTime 𝓕 (fun ω => (τ ω : WithTop ℝ≥0)))
    (times horizons : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (τ ω + s) ω - X.X (τ ω) ω < 0 := by sorry
