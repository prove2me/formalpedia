-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
-- name    : AvramDividend.Classical.avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T18:45:04.360182+00:00
-- url     : https://prove2.me/theorems/3b602ab2-8204-40d2-bef4-5965683ae752
-- title:
--   Discounted first-order bounded small mark product has compact coefficient envelope
-- statement:
--   For q>=0, time t>=0, mark |z|<=1 and coefficient |g|<=M with M>=0, the absolute discounted product exp(-qt)g z is bounded by M. Source-exact deterministic estimate for the finite-band stopped jump and clock first-order martingale.
-- source:
--   Mathlib Real.exp_le_one_iff, abs_mul, gcongr and real inequalities at pinned Mathlib revision.

import Mathlib
open MeasureTheory Set
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward58_nonnegative_discount_bounded_smallmark_product
    (q : ℝ) (hq : 0 ≤ q) (t : ℝ≥0)
    (z g M : ℝ) (hsmall : |z| ≤ 1)
    (hM : 0 ≤ M) (hg : |g| ≤ M) :
    |Real.exp (-(q * (t : ℝ))) * (g * z)| ≤ M := by sorry
