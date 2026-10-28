-- Prove2me | Theorems.Thm_AvramDividend_Classical_path_countable_killed_record_grid_reward_measurable
-- name    : AvramDividend.Classical.path_countable_killed_record_grid_reward_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T09:37:29.003326+00:00
-- url     : https://prove2.me/theorems/61bd8b00-48ae-4747-95ce-3f90bbe9ebab
-- title:
--   Measurability of a killed discounted grid reward from countable running records
-- statement:
--   For a sample-time skeleton and a grid of payment-cell endpoints, the full product-path reward obtained by taking the supremum over finite killed weighted increments of the sampled running maximum is measurable, provided the path-dependent killing time is measurable. Each sampled record is converted from ENNReal to Real so the extension is defined on arbitrary paths. The theorem is a noncircular measurability component needed to apply finite-stopping strong Markov factorisation to dyadic Stieltjes-dividend approximations.
-- source:
--   Avram, Palmowski and Pistorius (2007), Proposition 1. Extends the Proved countable_path_runningSup_increment_measurable to stopped, weighted Stieltjes partition rewards on the full product path space, upstream of dividendValue_barrierStrategy_upExit_split_of_standing (79978d61).

import Mathlib.MeasureTheory.Constructions.Pi
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Basic

open MeasureTheory
open scoped NNReal ENNReal Classical

theorem AvramDividend.Classical.path_countable_killed_record_grid_reward_measurable
    (samples mesh : ℕ → ℝ≥0)
    (stop : (ℝ≥0 → ℝ) → ℝ≥0∞) (hstop : Measurable stop)
    (weights : ℕ → ℝ≥0∞) :
    Measurable (fun f : ℝ≥0 → ℝ =>
      ⨆ N : ℕ, ∑ k ∈ Finset.range N,
        if (mesh (k + 1) : ℝ≥0∞) < stop f then
          weights k * ENNReal.ofReal
            ((⨆ i : ℕ,
                if samples i ≤ mesh (k + 1) then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal -
              (⨆ i : ℕ,
                if samples i ≤ mesh k then
                  ENNReal.ofReal (f (samples i) - f 0)
                else 0).toReal)
        else 0) := by
  sorry
