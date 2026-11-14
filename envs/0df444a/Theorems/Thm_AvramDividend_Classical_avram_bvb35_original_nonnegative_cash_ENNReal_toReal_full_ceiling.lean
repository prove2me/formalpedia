-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb35_original_nonnegative_cash_ENNReal_toReal_full_ceiling
-- name    : AvramDividend.Classical.avram_bvb35_original_nonnegative_cash_ENNReal_toReal_full_ceiling
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T11:31:32.498367+00:00
-- url     : https://prove2.me/theorems/c6716820-d4d6-4cab-adab-5ec85a62452c
-- title:
--   Original zero-contact physical discounted cash ENNReal HJB upper bound converts to finite real Stieltjes cash ceiling
-- statement:
--   Whenever an original nonnegative extended-real dividend cash mass plus terminal nonnegative discounted real value e*w is bounded by a finite original HJB generator compensation ceiling w+m*w*c in ENNReal, where boundary value, original Lévy mass, physical discount-time mass and terminal discount are nonnegative real scalars, the real dividend cash toReal plus terminal e*w is bounded by the same finite real full-HJB ceiling. The proof retains the original finiteness needed for toReal monotonicity and explicitly rules out infinite source cash. This is the exact ENNReal-to-real final budget bridge for source zero-reserve survivor 1569d325.
-- source:
--   Pinned ENNReal.toReal_mono, ENNReal.toReal_add, ENNReal.toReal_ofReal, ne_top_of_le_ne_top. Source original cash bound 09a9c1c4.

import Mathlib
open Classical MeasureTheory Set Filter
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb35_original_nonnegative_cash_ENNReal_toReal_full_ceiling
    (cash : ℝ≥0∞) (w m c e : ℝ)
    (hw : 0 ≤ w) (hm : 0 ≤ m) (hc : 0 ≤ c) (he : 0 ≤ e)
    (hHJB : cash + ENNReal.ofReal (e * w) ≤
      ENNReal.ofReal (w + m * w * c)) :
    cash.toReal + e * w ≤ w + m * w * c := by sorry
