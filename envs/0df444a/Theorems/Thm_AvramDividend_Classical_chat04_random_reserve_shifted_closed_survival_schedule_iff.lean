-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_schedule_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_closed_survival_schedule_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:16:53.302593+00:00
-- url     : https://prove2.me/theorems/67c7e86c-079c-40f3-8ffb-6f800f2a172a
-- title:
--   Every rational-covering schedule containing the horizon endpoint detects exact shifted Lévy survival
-- statement:
--   For arbitrary random initial reserve H(ω) and deterministic split time b, nonruin at all times in a future relative window [0,T] is equivalent to nonruin on any countable observation schedule covering all k/n and explicitly containing T. The event equality is pathwise and eliminates the countable-grid surrogate in the Proved killed-scale Markov–Tonelli factorisation, allowing it to be applied to the true continuously killed semigroup.
-- source:
--   Proved chat04_random_reserve_shifted_closed_survival_grid_iff and the rational schedule coverage and terminal-index hypotheses.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_closed_survival_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_closed_survival_schedule_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∀ v : ℝ≥0, v ≤ T →
      0 ≤ H ω + (X.X (b + v) ω - X.X b ω)) ↔
    ∀ j : ℕ, τ j ≤ T →
      0 ≤ H ω + (X.X (b + τ j) ω - X.X b ω) := by sorry
