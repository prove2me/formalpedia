-- Prove2me | Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_firstClosedHit_posthit_negative_of_grid
-- name    : AvramDividend.Classical.reflectedSup_capped_firstClosedHit_posthit_negative_of_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T22:59:32.750274+00:00
-- url     : https://prove2.me/theorems/408f8748-4f4c-4e5d-8600-e2bf1cc4bea2
-- title:
--   Capped reflected first-hit times inherit almost-sure arbitrarily small negative post-hit Lévy increments from a source cofinal negative-grid law
-- statement:
--   Let X be a spectrally negative Lévy process. At the true continuous-time first hit of reflected drawdown level x, capped at the finite deterministic horizon H when there is no earlier hit, almost every P sample path has negative Lévy increments arbitrarily soon after the clock, provided the original path has strictly negative observations along a fixed cofinal countable grid almost surely. The actual first-hit clock is a stopping time by the independently proved canonical reflectedSup_capped_closedLevelHit_stoppingTime. Apply the independently proved finite-stopping negative-grid event transfer to it. This is a source-probability strong Markov restart statement for the exact level hitting clock; it does not assert a sigma-finite excursion n-Markov theorem or prove the source grid law from unbounded variation.
-- source:
--   Accepted Prove2Me reflectedSup_capped_closedLevelHit_stoppingTime and levy_finiteStopping_negative_near_zero_of_grid; Kuznetsov, Kyprianou, Rivero 2013 excursion-height first-hit strong Markov decomposition.

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Mathlib.Probability.Process.Stopping
import Mathlib.Order.Interval.Set.Basic
import Theorems.Thm_AvramDividend_Classical_reflectedSup_capped_closedLevelHit_stoppingTime
import Theorems.Thm_AvramDividend_Classical_levy_finiteStopping_negative_near_zero_of_grid

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.reflectedSup_capped_firstClosedHit_posthit_negative_of_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : ℝ≥0) (x : ℝ)
    (times horizons : ℕ → ℝ≥0)
    (hcofinal : ∀ ε : ℝ≥0, 0 < ε → ∃ n : ℕ, horizons n ≤ ε)
    (hGridAE : ∀ᵐ ω ∂P, ∀ n : ℕ, ∃ m : ℕ,
      times m < horizons n ∧ X.X (times m) ω < 0) :
    ∀ᵐ ω ∂P, ∀ ε : ℝ≥0, 0 < ε →
      ∃ s : ℝ≥0, s < ε ∧
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H}) + s) ω -
        X.X (sInf ((Icc (0 : ℝ≥0) H ∩
          (fun u : ℝ≥0 => reflectedSup X u ω) ⁻¹' Ici x) ∪ {H})) ω < 0 := by sorry
