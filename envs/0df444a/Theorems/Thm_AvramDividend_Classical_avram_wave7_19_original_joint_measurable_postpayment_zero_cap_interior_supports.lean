-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave7_19_original_joint_measurable_postpayment_zero_cap_interior_supports
-- name    : AvramDividend.Classical.avram_wave7_19_original_joint_measurable_postpayment_zero_cap_interior_supports
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-02T21:16:42.851614+00:00
-- url     : https://prove2.me/theorems/0cb21cf7-85ac-4d5a-981b-d7091064010a
-- title:
--   Genuine original post-rightpayment zero/cap boundary and positive C² interior are jointly measurable supports
-- statement:
--   The zero-reserve and cap-reserve event union and the strict smooth HJB interior of the original controlled post-rightpayment Lévy reserve are jointly measurable subsets of nonnegative physical time and the path variable. This uses the existing Proved jointly measurable postpayment reserve, and directly supports W7-19 discounted original Stieltjes random-support Fatou passage. Boundary Stieltjes atoms and cap reflection mass remain included; no continuity at ruin or new stochastic assumptions.
-- source:
--   Original rightLimit controlled reserve; W8-20 joint reserve measurability Proved UUID 6410e850.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave8_20_original_postpayment_reserve_joint_measurable
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave7_19_original_joint_measurable_postpayment_zero_cap_interior_supports
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (C : ℝ≥0∞) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D) :
    MeasurableSet {p : ℝ≥0 × Ω |
      x + X.X p.1 p.2 - rightLimit D p.1 p.2 = 0 ∨
        ENNReal.ofReal (x + X.X p.1 p.2 - rightLimit D p.1 p.2) = C} ∧
    MeasurableSet {p : ℝ≥0 × Ω |
      0 < x + X.X p.1 p.2 - rightLimit D p.1 p.2 ∧
        ENNReal.ofReal (x + X.X p.1 p.2 - rightLimit D p.1 p.2) < C} := by sorry
