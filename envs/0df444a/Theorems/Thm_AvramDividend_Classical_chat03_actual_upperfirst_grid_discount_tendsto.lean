-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat03_actual_upperfirst_grid_discount_tendsto
-- name    : AvramDividend.Classical.chat03_actual_upperfirst_grid_discount_tendsto
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-21T20:55:24.120989+00:00
-- url     : https://prove2.me/theorems/6af82499-afc8-4539-b788-acb841bc161b
-- title:
--   Actual sampled strict upper-first discount converges to official continuous upper-first reward
-- statement:
--   For a spectrally negative Lévy sample path with separated strict lower and upper barriers, the exact upper-first discounted reward computed from the indexed ENNReal infima of all strict uniform-grid upper and lower passages converges to the official continuous upper-first discounted reward. Both finite and infinite passage clocks are covered. This removes abstract grid-clock convergence assumptions by applying already Proved exact clock convergence and no-upper-exit persistence theorems.
-- source:
--   Composition of Proved chat03_official_upper_grid_clock_tendsto, chat03_official_lower_grid_clock_tendsto, chat03_official_no_upper_exit_grid_inf_top and chat03_official_grid_discount_tendsto_from_clock_convergence. No new stochastic martingale assumption.

import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_chat03_official_upper_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_lower_grid_clock_tendsto
import Theorems.Thm_AvramDividend_Classical_chat03_official_no_upper_exit_grid_inf_top
import Theorems.Thm_AvramDividend_Classical_chat03_official_grid_discount_tendsto_from_clock_convergence
import Mathlib.Topology.Instances.ENNReal.Lemmas

open MeasureTheory Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat03_actual_upperfirst_grid_discount_tendsto
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (lower upper : ℝ) (hsep : lower < upper)
    (q : ℝ) (mesh : ℕ → ℝ≥0)
    (hpos : ∀ n, 0 < mesh n)
    (hzero : Tendsto mesh atTop (𝓝 (0 : ℝ≥0))) :
    Tendsto
      (fun n =>
        if (⨅ k : ℕ,
          if upper < X.X ((k : ℝ≥0) * mesh n) ω then
            (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
          else ∞) <
          (⨅ k : ℕ,
            if X.X ((k : ℝ≥0) * mesh n) ω < lower then
              (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
            else ∞) then
          ENNReal.ofReal (Real.exp (-(q * ENNReal.toReal
            (⨅ k : ℕ,
              if upper < X.X ((k : ℝ≥0) * mesh n) ω then
                (((k : ℝ≥0) * mesh n) : ℝ≥0∞)
              else ∞))))
        else 0) atTop
      (𝓝 (if twoSidedExitUpTime X upper ω <
          twoSidedExitDownTime X lower ω then
        ENNReal.ofReal (Real.exp
          (-(q * ENNReal.toReal (twoSidedExitUpTime X upper ω))))
        else 0)) := by
  sorry
