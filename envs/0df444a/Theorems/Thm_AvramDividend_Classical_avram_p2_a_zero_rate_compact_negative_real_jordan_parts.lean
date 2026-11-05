-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_a_zero_rate_compact_negative_real_jordan_parts
-- name    : AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_real_jordan_parts
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T07:42:07.554685+00:00
-- url     : https://prove2.me/theorems/f764b4ed-d83c-4725-bf56-62b0599b4a93
-- title:
--   Signed original compact-negative tests split into compact-negative nonnegative parts
-- statement:
--   Every continuous real test with compact support strictly within the negative reals decomposes into the difference of its continuous nonnegative positive and negative parts. Both parts retain compact support strictly within the negative reals. This allows positive original jump-sum ENNReal mean identities to determine signed compact-test measures without boundary-indicator convergence.

import Mathlib.Topology.Algebra.Support
import Mathlib.Order.Lattice
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set Topology AvramDividend.Classical

theorem AvramDividend.Classical.avram_p2_a_zero_rate_compact_negative_real_jordan_parts
    (g : ℝ → ℝ) (hg : Continuous g)
    (hc : IsCompact (tsupport g))
    (hneg : tsupport g ⊆ Iio (0 : ℝ)) :
    ∃ gp gn : ℝ → ℝ,
      Continuous gp ∧ IsCompact (tsupport gp) ∧ tsupport gp ⊆ Iio (0 : ℝ) ∧
      Continuous gn ∧ IsCompact (tsupport gn) ∧ tsupport gn ⊆ Iio (0 : ℝ) ∧
      (∀ x : ℝ, 0 ≤ gp x ∧ 0 ≤ gn x ∧ g x = gp x - gn x) := by sorry
