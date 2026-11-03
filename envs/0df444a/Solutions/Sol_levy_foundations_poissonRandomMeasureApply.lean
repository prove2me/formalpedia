-- Prove2me | solution 1 for levy_foundations_poissonRandomMeasureApply
-- status  : ACCEPTED   (prove)
-- author  : @WillR
-- created : 2026-10-26T23:49:14.488564+00:00
-- url     : https://prove2.me/submissions/39afc081-002d-48e1-b7d8-c0fbe0d8b08d

import Mathlib.MeasureTheory.Integral.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Dirac
import Definitions.Def_levy_foundations_poissonRandomMeasure
import Definitions.Def_levy_foundations_thinnedCount
import Theorems.Thm_levy_foundations_thinnedCountToENNReal

set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set
open scoped ENNReal

theorem solution
    {Ω E : Type*} [MeasurableSpace E]
    (K : ℕ → Ω → ℕ) (X : ℕ → ℕ → Ω → E)
    (ω : Ω) {A : Set E} (hA : MeasurableSet A) :
    LevyFoundations.poissonRandomMeasure K X ω A =
      ∑' k : ℕ, (LevyFoundations.thinnedCount K X A k ω : ℝ≥0∞) := by
  classical
  rw [LevyFoundations.poissonRandomMeasure, Measure.sum_apply _ hA]
  refine tsum_congr fun k => ?_
  rw [Measure.sum_apply _ hA]
  have hterm : ∀ n, (if n < K k ω then Measure.dirac (X k n ω) else 0) A =
      if n < K k ω then A.indicator (1 : E → ℝ≥0∞) (X k n ω) else 0 := by
    intro n
    rw [apply_ite (fun ν : Measure E => ν A), Measure.dirac_apply' _ hA,
      Measure.coe_zero, Pi.zero_apply]
  simp_rw [hterm]
  rw [tsum_eq_sum (s := Finset.range (K k ω)) fun n hn => by
    rw [if_neg (by simpa [Finset.mem_range] using hn)]]
  rw [levy_foundations_thinnedCountToENNReal]
  refine Finset.sum_congr rfl fun n hn => ?_
  rw [if_pos (by simpa [Finset.mem_range] using hn)]
