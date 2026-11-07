-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_grid4_allcap_expanding_compact_band_witnesses
-- name    : AvramDividend.Classical.avram_p3_grid4_allcap_expanding_compact_band_witnesses
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-06T06:25:48.699194+00:00
-- url     : https://prove2.me/theorems/b8a61187-0302-46ea-a88b-d811aa697355
-- title:
--   All-cap original BV compact interior reserve bands for indexed compensated jump and HJB source
-- statement:
--   Explicit finite and infinite cap split constructs positive indexed compact interior reserve bands a_n,b_n meeting the complete geometric hypotheses of Proved original BV indexed compensated jump/HJB source 6d66798c, for every C>0. The finite-cap branch imports the independently published geometry reduction; no original stopped cash/source identity is claimed.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Set
open scoped ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_grid4_allcap_expanding_compact_band_witnesses
    (C : ℝ≥0∞) (hC : 0 < C) :
    ∃ a b : ℕ → ℝ,
      (∀ n, 0 < a n) ∧
      (∀ n, a n ≤ 2) ∧
      (∀ n, a n ≤ b n) ∧
      (∀ n, Icc (a n / 2) (b n) ⊆
        {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) := by sorry
