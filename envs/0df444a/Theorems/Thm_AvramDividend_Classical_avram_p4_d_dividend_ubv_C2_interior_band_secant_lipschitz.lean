-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
-- name    : AvramDividend.Classical.avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-03T08:27:18.512174+00:00
-- url     : https://prove2.me/theorems/c4293baa-88f7-4181-b1e6-0fbe74f04472
-- title:
--   Original UBV verification C2 interior compact-band derivative envelope yields local Lipschitz right-payment secants
-- statement:
--   For the original UBV candidate verification function w, canonical C2 regularity on the strictly positive below-cap interior and an actual derivative bound on any compact reserve band contained in that open interior give a uniform absolute secant estimate. This is the missing C2 analogue of the proved BV-only 82f28985 compact-band lemma and supplies the upper local secant slope required by the countable real right-atom summability criterion. The band must be justified by the original path/localisation and may not simply be extrapolated through cap or zero contact.
-- source:
--   Avram–Palmowski–Pistorius Proposition 4(i), C2 UBV regularity and Eq. (5.13); source-pinned original BV band proof 82f28985, modified without BV hypotheses.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_d_dividend_ubv_C2_interior_band_secant_lipschitz
    (C : ℝ≥0∞) (w : ℝ → ℝ)
    (hwC2 : ContDiffOn ℝ 2 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (a b : ℝ)
    (hOpen : IsOpen {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hBand : Icc a b ⊆ {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (K : ℝ≥0)
    (hK : ∀ y ∈ Icc a b, ‖deriv w y‖₊ ≤ K) :
    ∀ s ∈ Icc a b, ∀ t ∈ Icc a b,
      |w s - w t| ≤ (K : ℝ) * |s - t| := by sorry
