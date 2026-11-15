-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a253_Gauss_HJB_weighted_first_derivative_factor_product_identity
-- name    : AvramDividend.Classical.avram_ga_a253_Gauss_HJB_weighted_first_derivative_factor_product_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T08:45:20.889118+00:00
-- url     : https://prove2.me/theorems/e7150545-ed18-4fbe-b9a4-2ba6bf7a75b7
-- title:
--   Product identity between the first-order HJB integrating factor and exponentially rescaled value derivative.
-- statement:
--   Product identity between the first-order HJB integrating factor and exponentially rescaled value derivative. Source step in the original Gaussian HJB near-zero one-sided upper control, used with a249/a250/a251.
-- source:
--   Source-exact zero-jump Gaussian HJB origin weighted derivative comparison

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_ga_a253_Gauss_HJB_weighted_first_derivative_factor_product_identity
    (f fp alpha beta y : ℝ) :
    Real.exp (-alpha*y)*(fp-alpha*f) =
      Real.exp ((beta-alpha)*y)*
        (Real.exp (-beta*y)*(fp-alpha*f)) := by sorry
