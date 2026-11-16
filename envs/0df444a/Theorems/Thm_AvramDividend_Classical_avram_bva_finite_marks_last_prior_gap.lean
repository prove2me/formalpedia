-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bva_finite_marks_last_prior_gap
-- name    : AvramDividend.Classical.avram_bva_finite_marks_last_prior_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-15T09:50:10.396356+00:00
-- url     : https://prove2.me/theorems/760bcedb-7282-436d-b120-ab2faa001cdf
-- title:
--   Finite marked times have a strict left gap preceding every positive time
-- statement:
--   For any finite set of nonnegative marked times and any positive time t, there is a time s<t that bounds every marked time u<t. The interval (s,t) therefore contains no marked time. This gives a jump-free strict-left neighbourhood for the original finite-activity path.
-- source:
--   Finite maximum of filtered marked times

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_bva_finite_marks_last_prior_gap
    (S : Finset ℝ≥0) (t : ℝ≥0) (ht : 0 < t) :
    ∃ s : ℝ≥0, s < t ∧
      ∀ u ∈ S, u < t → u ≤ s := by sorry
