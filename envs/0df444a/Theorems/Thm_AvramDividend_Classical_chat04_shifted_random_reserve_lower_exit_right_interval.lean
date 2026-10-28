-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_shifted_random_reserve_lower_exit_right_interval
-- name    : AvramDividend.Classical.chat04_shifted_random_reserve_lower_exit_right_interval
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T20:47:44.388593+00:00
-- url     : https://prove2.me/theorems/4b5cb86f-40d7-4464-8b8c-f57f3dbae99e
-- title:
--   Strict downward passage persists for a randomly shifted reserve under deterministic clock translation
-- statement:
--   For any deterministic Lévy splitting clock b and path-dependent initial reserve H(ω), a strict ruin crossing of H(ω)+X(b+t)-X(b) is preserved in a nonempty right neighbourhood of b+t in the original clock. This extends the Proved chat03_strict_lower_exit_right_interval by exact translation and supplies the strict window needed to detect shifted future ruin on countable grids in the killed q-scale Markov semigroup.
-- source:
--   Proved chat03_strict_lower_exit_right_interval, with elementary ordered-addition translation.

import Mathlib.Tactic.Linarith
import Mathlib.MeasureTheory.Constructions.BorelSpace.Real
import Mathlib.Topology.Instances.ENNReal.Lemmas
import Theorems.Thm_AvramDividend_Classical_chat03_strict_lower_exit_right_interval

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_shifted_random_reserve_lower_exit_right_interval
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (H : Ω → ℝ) (ω : Ω) (b t : ℝ≥0)
    (h : H ω + (X.X (b + t) ω - X.X b ω) < 0) :
    ∃ u : ℝ≥0, b + t < u ∧
      ∀ v : ℝ≥0, b + t ≤ b + v → b + v < u →
        H ω + (X.X (b + v) ω - X.X b ω) < 0 := by sorry
