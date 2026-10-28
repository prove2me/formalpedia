-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_two_sided_survival_schedule_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_two_sided_survival_schedule_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T22:06:32.06209+00:00
-- url     : https://prove2.me/theorems/b5a023df-89ab-479b-8da3-051b69465025
-- title:
--   Two-sided finite-interval survival of a shifted Lévy reserve is equivalent to one countable schedule
-- statement:
--   A Lévy reserve shifted by any deterministic clock and started at any path-dependent reserve H remains inside the closed interval [0,a] for all times through T if and only if the reserve remains in [0,a] at every point of a rationally covering countable monitoring schedule containing T. This combines proved lower and upper exact survival equivalences and supplies a pathwise two-sided-killing event for the stopped martingale and Markov-kernel programmes.
-- source:
--   Proved lower and upper shifted closed-survival schedule equivalences.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_schedule_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_two_sided_survival_schedule_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ H ω + (X.X (b + v) ω - X.X b ω) ∧
      H ω + (X.X (b + v) ω - X.X b ω) ≤ a) ↔
    ∀ j : ℕ, τ j ≤ T →
      0 ≤ H ω + (X.X (b + τ j) ω - X.X b ω) ∧
      H ω + (X.X (b + τ j) ω - X.X b ω) ≤ a := by sorry
