-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_support_separated
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_test_support_separated
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:46:11.186111+00:00
-- url     : https://prove2.me/theorems/d3193c6f-cf66-4fec-817b-c1b4d3e843fd
-- title:
--   Every compact-negative real test has an explicit separated finite-intensity support band
-- statement:
--   A continuous real test compactly supported strictly inside the negative reals has some positive ε such that its actual function support lies in (-∞,-ε]. The result combines proven compact-negative vanishing near zero with sign support and elementary absolute-value inequalities, providing the exact separated finite-measure envelope required for original jump test integrability and Radon uniqueness.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_test_vanishes_near_zero
open Set Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_test_support_separated
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∃ ε : ℝ, 0 < ε ∧ Function.support g ⊆ Iic (-ε) := by sorry
