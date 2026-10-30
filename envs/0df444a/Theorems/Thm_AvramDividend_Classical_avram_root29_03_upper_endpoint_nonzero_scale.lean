-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_root29_03_upper_endpoint_nonzero_scale
-- name    : AvramDividend.Classical.avram_root29_03_upper_endpoint_nonzero_scale
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-29T08:33:42.543479+00:00
-- url     : https://prove2.me/theorems/290a87bd-c901-448e-95b1-dc1687785aa9
-- title:
--   Strict two-sided exit ratio at upper endpoint from interior with only nonzero scale
-- statement:
--   For a genuine spectrally negative Levy process with nonnegative discount and q-scale function W, a positive barrier with W(a) nonzero, and the strict two-sided exit scale-ratio identity at every interior reserve, the same identity holds at x=a. No Standing, bounded-variation, or upward-regularity hypothesis is imposed.
-- source:
--   Strengthening of proved Standing-only adapter 01a564c9, needed by the no-Standing unbounded-variation canonical integration 2dcc8bcc. It uses solely proved monotonicity cd747fb7, expectation bound dde72b60, continuity of IsScaleFunction, and the stated nonzero denominator. A proved positivity theorem e50526dc supplies W(a) != 0 in the UBV branch; no Open stopped-scale theorem is imported.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_discounted_strict_exit_monotone_initial_reserve
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_le_one

open AvramDividend.Classical MeasureTheory Set Filter Topology
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_root29_03_upper_endpoint_nonzero_scale
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 ≤ q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a : ℝ) (ha : 0 < a) (hWa : W a ≠ 0)
    (hInterior : ∀ y : ℝ, 0 < y → y < a →
      twoSidedExitExpectation X q a y = ENNReal.ofReal (W y / W a)) :
    twoSidedExitExpectation X q a a = ENNReal.ofReal (W a / W a) := by sorry
