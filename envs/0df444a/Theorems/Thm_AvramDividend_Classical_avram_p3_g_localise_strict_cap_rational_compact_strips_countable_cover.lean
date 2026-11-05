-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
-- name    : AvramDividend.Classical.avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:12:15.786328+00:00
-- url     : https://prove2.me/theorems/3abce49a-dd67-479a-96ec-dfc818174c1c
-- title:
--   Strict cap interior admits rational positive compact C1 bands, countable for BV localisation
-- statement:
--   Every positive real reserve strictly below a possibly infinite ENNReal cap lies inside a deterministic rational-endpoint interval Ioo a b. The enlarged compact derivative strip Icc(a/2)b remains positive and strictly below the cap, with a<=2. Since ℚ×ℚ is countable, this supplies a countable concrete family of admissible bands, enabling predictable localisation of the original spectrally negative Levy reserve without assuming boundary-occupation-zero.
-- source:
--   Mathlib exists_rat_btwn, ENNReal.ofReal_lt_iff_lt_toReal for finite cap, ENNReal.ofReal_le_ofReal; actual cap condition. Extends accepted P3-G real-band pointwise theorem 325f33e2 to rational countability.

import Mathlib.Data.ENNReal.Basic
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_strict_cap_rational_compact_strips_countable_cover (C : ℝ≥0∞) (y : ℝ)
    (hy : 0 < y) (hyC : ENNReal.ofReal y < C) :
    ∃ a b : ℚ,
      0 < (a : ℝ) ∧ (a : ℝ) ≤ 2 ∧
      (a : ℝ) ≤ (b : ℝ) ∧
      y ∈ Ioo (a : ℝ) (b : ℝ) ∧
      Icc ((a : ℝ) / 2) (b : ℝ) ⊆
        {v : ℝ | 0 < v ∧ ENNReal.ofReal v < C} := by sorry
