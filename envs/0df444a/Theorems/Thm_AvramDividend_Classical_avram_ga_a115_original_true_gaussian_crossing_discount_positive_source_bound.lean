-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a115_original_true_gaussian_crossing_discount_positive_source_bound
-- name    : AvramDividend.Classical.avram_ga_a115_original_true_gaussian_crossing_discount_positive_source_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T09:51:02.136227+00:00
-- url     : https://prove2.me/theorems/5ec8ddba-c45f-4b59-bd5b-90a830ac2423
-- title:
--   Actual Gaussian stopped crossing positive discounted source increment bounded by undiscounted absolute displacement and compensator
-- statement:
--   The original physically stopped Gaussian crossing source discount at any random nonnegative stopping clock is between zero and one when the discount rate is nonnegative. Thus a positive discounted spatial source value increment with an HJB compensator is bounded by absolute undiscounted spatial value displacement plus absolute compensator, directly suited to the original one-sided expected-L1 crossing budget.
-- source:
--   Original Avram Gaussian positive-interior b0 true random clipped crossing cell and ga100 positive source value envelope.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a115_original_true_gaussian_crossing_discount_positive_source_bound
    (q : ℝ) (hq : 0 ≤ q) (ρ : ℝ≥0) (a h : ℝ) :
    max (Real.exp (-(q * (ρ : ℝ))) * a - h) 0 ≤
      |a| + |h| := by sorry
