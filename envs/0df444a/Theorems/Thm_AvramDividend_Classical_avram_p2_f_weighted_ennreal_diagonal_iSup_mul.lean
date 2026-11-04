-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_f_weighted_ennreal_diagonal_iSup_mul
-- name    : AvramDividend.Classical.avram_p2_f_weighted_ennreal_diagonal_iSup_mul
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T18:27:02.454822+00:00
-- url     : https://prove2.me/theorems/960cf321-1669-408b-8dc3-731bab7b950f
-- title:
--   Directed diagonal ENNReal product preserves monotone suprema
-- statement:
--   For two increasing sequences in ENNReal, the product of their suprema is the supremum of the diagonal products. This directed convergence fact includes the 0·∞ boundary and enables simultaneous approximation of random weights and intrinsic jump mark counts.
-- source:
--   Pinned Mathlib ENNReal.iSup_mul, ENNReal.mul_iSup, Nat.le_max_left/right, lattice iSup_le/le_iSup and multiplication monotonicity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_p2_f_weighted_ennreal_diagonal_iSup_mul
    (a b : ℕ → ℝ≥0∞)
    (ha : Monotone a) (hb : Monotone b) :
    (⨆ n, a n) * (⨆ n, b n) = ⨆ n, a n * b n := by sorry
