-- Prove2me | Theorems.Thm_AvramDividend_Classical_gaussian_double_tail_unweighted_atom_area
-- name    : AvramDividend.Classical.gaussian_double_tail_unweighted_atom_area
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-22T11:46:23.547497+00:00
-- url     : https://prove2.me/theorems/35d87cb0-86ed-455e-9b6c-8415a5712abb
-- title:
--   Exact unweighted triangular Gaussian double-tail area
-- statement:
--   The integral of z−t across a zero-to-z interval is z squared divided by two. The identity remains valid for negative z because interval integrals are oriented. It is the scalar area identity in the Tonelli proof of global Gaussian Esscher double-tail L1 integrability.
-- source:
--   Mathlib intervalIntegral.integral_sub, intervalIntegral.integral_const and integral_id

import Mathlib
open MeasureTheory intervalIntegral

theorem AvramDividend.Classical.gaussian_double_tail_unweighted_atom_area (z : ℝ) : (∫ t in (0 : ℝ)..z, z - t) = z ^ 2 / 2 := by sorry
