-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a34_original_finitecap_ruin_negative_crossing_positive_caplinear_zero
-- name    : AvramDividend.Classical.avram_a34_original_finitecap_ruin_negative_crossing_positive_caplinear_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T12:52:07.223178+00:00
-- url     : https://prove2.me/theorems/36dfb116-ae36-4670-b15f-766d0b0c5f53
-- title:
--   Original finitecap spatial ruin-crossing contributes zero positive caplinear residual
-- statement:
--   For an actual nonnegative pre-ruin postpayment reserve y≤c with nonnegative HJB candidate w(y), any true original Gaussian or spectrally negative Lévy spatial increment r sending y+r strictly below ruin threshold zero contributes exactly zero to the positive part of the caplinear spatial correction max(V(y+r)−w(y),0). This isolates ruin-crossing cells from compact positive-band spatial L1 arguments, without requiring w(0)=0 or continuity of the zero-extended w across ruin. The original standing HJB conditions include w(z)=0 for z<0 and w(y)≥0 on the pre-ruin path.
-- source:
--   Actual original finitecap stopped physical ruin crossing boundary spatial positive error vanishes exactly (scalar source transferable to same-X cells).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical

theorem AvramDividend.Classical.avram_a34_original_finitecap_ruin_negative_crossing_positive_caplinear_zero
    (w : ℝ → ℝ) (c : ℝ) (hc : 0 ≤ c)
    (hw_neg : ∀ z : ℝ, z < 0 → w z = 0)
    (y r : ℝ) (hy : 0 ≤ y) (hyc : y ≤ c)
    (hwy : 0 ≤ w y) (hneg : y + r < 0) :
    max ((if y + r ≤ c then w (y + r)
      else w c + (y + r - c)) - w y) 0 = 0 := by sorry
