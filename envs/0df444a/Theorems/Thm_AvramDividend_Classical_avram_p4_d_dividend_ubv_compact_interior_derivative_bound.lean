-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_compact_interior_derivative_bound
-- name    : AvramDividend.Classical.avram_p4_d_dividend_ubv_compact_interior_derivative_bound
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T00:16:44.592195+00:00
-- url     : https://prove2.me/theorems/8e186779-53af-4f29-ab64-89b03a4d36ba
-- title:
--   Original UBV C2 interior regularity gives a finite uniform derivative bound on every compact reserve band
-- statement:
--   For the exact source UBV C2 HJB interior 0<y and ofReal y<C, every closed real interval contained in that interior has a finite nonnegative uniform absolute derivative bound. The result follows from source-Proved interior openness, derivative continuity, compactness, and does not require the BV hypothesis present in the earlier source theorem. It supplies the local L1 coefficient for the P4-D signed right-payment Lipschitz estimate under interior localisation.
-- source:
--   Proved original cap-interior openness theorem avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen; pinned Mathlib ContDiffOn deriv continuity and compact interval derivative norm bound; adapted from accepted 07ca388c proof without BV premise.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave6_chat09_ENNReal_positive_cap_interior_isOpen
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_ubv_compact_interior_derivative_bound
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ) (hab : a ≤ b)
    (hBand : Icc a b ⊆
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C}) :
    ∃ K : ℝ, 0 ≤ K ∧
      ∀ y ∈ Icc a b, |deriv w y| ≤ K := by sorry
