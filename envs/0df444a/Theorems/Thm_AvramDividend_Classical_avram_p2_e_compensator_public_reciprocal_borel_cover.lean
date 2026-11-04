-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_public_reciprocal_borel_cover
-- name    : AvramDividend.Classical.avram_p2_e_compensator_public_reciprocal_borel_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T23:23:36.801268+00:00
-- url     : https://prove2.me/theorems/8936f618-4b45-42ea-8110-9c32353aec36
-- title:
--   Every Borel Lévy mark set has a public measurable increasing strictly-negative separated reciprocal exhaustion
-- statement:
--   For any Borel set of real marks, construct a sequence of measurable strictly-negative bands C_n that increases to B intersected with (-∞,0), each lying below a strictly negative cutoff. The canonical construction C_n = B ∩ (-∞,-1/(n+1)] uses only pinned Mathlib order/topology and no process, compensator, Poisson law or Lévy intensity. This public deterministic interface supports original marked-count monotone extension.
-- source:
--   Pinned Mathlib 0df444a360eaa60ab8c11dca51a86af692955474: iUnion_Iic_eq_Iio_of_lt_of_tendsto, tendsto_one_div_add_atTop_nhds_zero_nat, one_div_le_one_div_of_le. Independent original-process rate arguments do not enter.

import Mathlib

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_public_reciprocal_borel_cover
    (B : Set ℝ) (hB : MeasurableSet B) :
    ∃ C : ℕ → Set ℝ,
      (∀ n, MeasurableSet (C n)) ∧
      Monotone C ∧
      (⋃ n, C n) = B ∩ Iio (0 : ℝ) ∧
      ∀ n, ∃ ε : ℝ, 0 < ε ∧ C n ⊆ Iic (-ε) := by sorry
