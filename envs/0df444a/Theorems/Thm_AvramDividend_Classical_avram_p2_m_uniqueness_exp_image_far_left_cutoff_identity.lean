-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_m_uniqueness_exp_image_far_left_cutoff_identity
-- name    : AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_far_left_cutoff_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T08:03:08.96146+00:00
-- url     : https://prove2.me/theorems/bd25424a-9daf-4c8e-ab7e-d1850ca487c3
-- title:
--   Exact inverse-exponential tail cutoff for real measures
-- statement:
--   For any Borel measure σ and each natural cutoff n, the mass under σ.map exp of the positive interval (−∞, exp(−n)] equals the σ-mass of (−∞,−n]. This is the exact transport of the left tail to the logarithmic zero endpoint, without an assumed intensity or finite measure hypothesis.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.avram_p2_m_uniqueness_exp_image_far_left_cutoff_identity (σ : Measure ℝ) (n : ℕ) : (σ.map Real.exp) (Iic (Real.exp (-(n : ℝ)))) = σ (Iic (-(n : ℝ))) := by sorry
