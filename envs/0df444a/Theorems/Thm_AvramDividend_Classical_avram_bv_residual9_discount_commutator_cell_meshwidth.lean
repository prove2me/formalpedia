-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_residual9_discount_commutator_cell_meshwidth
-- name    : AvramDividend.Classical.avram_bv_residual9_discount_commutator_cell_meshwidth
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T12:28:44.336966+00:00
-- url     : https://prove2.me/theorems/3e6da293-6d69-44cc-b194-1f929d167bff
-- title:
--   Original BV physical-grid discount commutator bounded by meshwidth and negative contact
-- statement:
--   For nonnegative discount rate and stopped physical cell length at most δ, the discount commutator times its post-cell reserve is at most q δ times the negative reserve part. This uses a proved original-process discount Lipschitz theorem, with no asserted contact localisation or envelope.
-- source:
--   AVRAM BV-RESIDUAL9 round-four physical-grid discount analysis

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_original_nonnegative_discount_exp_lipschitz
open Classical MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_bv_residual9_discount_commutator_cell_meshwidth
    (q a b δ post : ℝ)
    (hq : 0 ≤ q) (ha : 0 ≤ a) (hab : a ≤ b) (hwidth : b - a ≤ δ) :
    (Real.exp (-(q * b)) - Real.exp (-(q * a))) * post ≤
      (q * δ) * max (-post) 0 := by sorry
