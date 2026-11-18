-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a27_real_unit_interval_power_lipschitz_20261117
-- name    : AvramDividend.Classical.avram_a27_real_unit_interval_power_lipschitz_20261117
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T23:36:35.273698+00:00
-- url     : https://prove2.me/theorems/62e24cbd-8405-4542-91ca-5617084bbef9
-- title:
--   Real powers on the unit interval are Lipschitz with exact natural exponent constant
-- statement:
--   For any two reals in the closed interval from zero to one, their nth powers differ by at most n times their original difference in absolute value. This is the deterministic key to the original marked jump PGF being Lipschitz in the count-generating parameter, with constant bounded by the original physical expected jump count.
-- source:
--   Pinned Mathlib abs_pow_sub_pow_le; order and nonnegative polynomial bounds.

import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Algebra.Order.Ring.Abs
import Mathlib.Algebra.Order.Monoid.Unbundled.Pow
import Mathlib.Tactic.Ring
open Real
noncomputable section

theorem AvramDividend.Classical.avram_a27_real_unit_interval_power_lipschitz_20261117
    (z w : ℝ) (hz : 0 ≤ z) (hz1 : z ≤ 1)
    (hw : 0 ≤ w) (hw1 : w ≤ 1) (n : ℕ) :
    |z ^ n - w ^ n| ≤ (n : ℝ) * |z - w| := by sorry
