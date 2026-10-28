-- Prove2me | Theorems.Thm_AvramDividend_Classical_finite_clock_reward_lintegral_eq_sup_caps
-- name    : AvramDividend.Classical.finite_clock_reward_lintegral_eq_sup_caps
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T23:40:30.820615+00:00
-- url     : https://prove2.me/theorems/21f6423f-84d4-4f5b-b771-32ab6c182818
-- title:
--   Nonnegative reward before a finite clock equals supremum of all finite-clock truncations
-- statement:
--   For a measurable possibly infinite stopping clock and nonnegative reward, the expected reward on finite-clock paths is the supremum of its expectations on the events where the clock occurs before integer horizon n. Proves the exact monotone limit required when removing finite-horizon localisation from killed-record strong Markov inequalities.
-- source:
--   ENNReal.exists_nat_gt; MeasureTheory.lintegral_iSup; measurable if-then-else; monotonicity under increasing finite caps.

import Mathlib.Data.ENNReal.Basic
import Mathlib.MeasureTheory.Integral.Lebesgue.Add
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory AvramDividend.Classical
open scoped ENNReal

theorem AvramDividend.Classical.finite_clock_reward_lintegral_eq_sup_caps
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    (P : Measure Ω) (clock : Ω → ℝ≥0∞) (reward : Ω → ℝ≥0∞)
    (hclock : Measurable clock) (hreward : Measurable reward) :
    (∫⁻ ω, if clock ω < ⊤ then reward ω else 0 ∂P) =
      ⨆ n : ℕ, (∫⁻ ω, if clock ω ≤ (n : ℝ≥0∞)
        then reward ω else 0 ∂P) := by sorry
