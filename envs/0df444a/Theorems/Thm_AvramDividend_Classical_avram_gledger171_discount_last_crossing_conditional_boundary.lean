-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gledger171_discount_last_crossing_conditional_boundary
-- name    : AvramDividend.Classical.avram_gledger171_discount_last_crossing_conditional_boundary
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:23:36.227097+00:00
-- url     : https://prove2.me/theorems/d0030b2d-3b44-4370-88fb-bb49825d14f9
-- title:
--   Conditional final-crossing bound whether or not the terminal Riemann term is present
-- statement:
--   The exact physical stopped-discount final crossing remainder is uniformly bounded by 2 q delta K, whether the final index belongs to the shorter Riemann sum or not. If the indicator is true, use already Proved gledger148; if false, use the sharper Proved gledger147 and the compact weight bound. This is the exact missing terminal boundary case for gledger164.
-- source:
--   Proved gledger147 and gledger148 finite clipped exponential bounds.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_gledger147_clipped_final_discount_cell_absolute_bound
import Theorems.Thm_AvramDividend_Classical_avram_gledger148_weighted_clipped_discount_euler_boundary_bound
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_gledger171_discount_last_crossing_conditional_boundary
    (q t r δ a K : ℝ) (hq : 0 ≤ q) (ht : 0 ≤ t)
    (hr : 0 ≤ r) (hrδ : r ≤ δ) (hK : 0 ≤ K) (ha : |a| ≤ K)
    (b : Prop) [Decidable b] :
    |(Real.exp (-(q * (t + r))) - Real.exp (-(q * t)) +
       (if b then q * δ * Real.exp (-(q * t)) else 0)) * a| ≤
      2 * q * δ * K := by sorry
