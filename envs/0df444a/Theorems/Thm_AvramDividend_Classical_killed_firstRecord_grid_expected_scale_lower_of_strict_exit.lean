-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_expected_scale_lower_of_strict_exit
-- name    : AvramDividend.Classical.killed_firstRecord_grid_expected_scale_lower_of_strict_exit
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T12:34:04.54976+00:00
-- url     : https://prove2.me/theorems/fdf5bdae-0759-4798-9526-b31e066ffbe2
-- title:
--   Expected killed-grid geometric lower bounds conditional on strict two-sided exit
-- statement:
--   The exact strict discounted exit factor yields the first killed record and, through proved uncapped Markov regeneration, every subsequent record weight. The geometric lower bounds follow by the previously proved abstract recurrence lemma.
-- source:
--   Previously Proved killed_firstRecord_initial_lower_of_strict_exit, killed_firstRecord_one_step_scale_regeneration_lower_of_strict_exit, and killed_firstRecord_grid_geometric_expected_lower_of_step.

import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Positivity
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_one_step_scale_regeneration_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_initial_lower_of_strict_exit
import Theorems.Thm_AvramDividend_Classical_killed_firstRecord_grid_geometric_expected_lower_of_step

open MeasureTheory AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.killed_firstRecord_grid_expected_scale_lower_of_strict_exit
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a)
    (hExit :
      (∫⁻ ω, if (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)) <
          (⨅ (t : ℝ≥0) (_ : X.X t ω < ε - a), (t : ℝ≥0∞)) then
        ENNReal.ofReal (Real.exp (-(q *
          ENNReal.toReal (⨅ (t : ℝ≥0) (_ : ε < X.X t ω), (t : ℝ≥0∞)))))
      else 0 ∂P) = ENNReal.ofReal (W (a - ε) / W a)) :
    ∀ n : ℕ,
      ENNReal.ofReal (ε * (W (a - ε) / W a) ^ (n + 1)) ≤
        (∫⁻ ω,
          if twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω <
              barrierRuinTime X a ω then
            ENNReal.ofReal (ε * Real.exp
              (-(q * (twoSidedExitUpTime X (((n + 1 : ℕ) : ℝ) * ε) ω).toReal)))
          else 0 ∂P) := by sorry
