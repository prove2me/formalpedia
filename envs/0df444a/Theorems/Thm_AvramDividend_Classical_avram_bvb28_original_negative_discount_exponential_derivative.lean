-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb28_original_negative_discount_exponential_derivative
-- name    : AvramDividend.Classical.avram_bvb28_original_negative_discount_exponential_derivative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T10:25:58.439522+00:00
-- url     : https://prove2.me/theorems/965914d9-04f0-4367-91fe-874728ce5828
-- title:
--   Original physical negative-discount exponential derivative at every real time
-- statement:
--   For every real physical discount parameter q and physical time t, the exact derivative of the original finite-horizon discount exp(-q t) is -q exp(-q t). This is a reusable pinned-Mathlib analytic atom for the original finite-horizon normalisation q times discounted time integral plus terminal discount equals one, which supplies the actual discount-clock premise for the source zero-contact compensated Stieltjes cash budget 09a9c1c4.
-- source:
--   Mathlib Real.hasDerivAt_exp via HasDerivAt.exp; original finite-horizon source normalisation 3ab4e2bc.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb28_original_negative_discount_exponential_derivative
    (q t : ℝ) :
    HasDerivAt (fun y : ℝ => Real.exp (-(q * y)))
      ((-q) * Real.exp (-(q * t))) t := by sorry
