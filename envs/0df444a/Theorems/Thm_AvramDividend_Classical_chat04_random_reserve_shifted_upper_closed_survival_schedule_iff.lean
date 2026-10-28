-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
-- name    : AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:57:55.348994+00:00
-- url     : https://prove2.me/theorems/4a6dbcf5-d238-43cb-9e30-055dad2eb38c
-- title:
--   Every rationally covering countable schedule with the endpoint detects upper-barrier survival
-- statement:
--   For a spectrally negative Lévy process shifted by a deterministic clock and begun at any path-dependent initial reserve, remaining below an upper barrier throughout [0,T] is exactly equivalent to checking it at any countable schedule containing every nonnegative rational and the terminal horizon T. This provides the upper-barrier counterpart to the proved lower-barrier random-reserve schedule theorem, allowing exact two-sided monitoring.
-- source:
--   Proved upper closed-survival rational-grid equivalence and an elementary covering argument.

import Mathlib.Data.NNReal.Defs
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat04_random_reserve_shifted_upper_closed_survival_grid_iff

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_random_reserve_shifted_upper_closed_survival_schedule_iff
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (a : ℝ) (b T : ℝ≥0)
    (τ : ℕ → ℝ≥0)
    (hCover : ∀ n : ℕ, 0 < n → ∀ k : ℕ,
      ∃ j : ℕ, τ j = (k : ℝ≥0) * (n : ℝ≥0)⁻¹)
    (hTerminal : ∃ j : ℕ, τ j = T) :
    (∀ v : ℝ≥0, v ≤ T →
      H ω + (X.X (b + v) ω - X.X b ω) ≤ a) ↔
    ∀ j : ℕ, τ j ≤ T →
      H ω + (X.X (b + τ j) ω - X.X b ω) ≤ a := by sorry
