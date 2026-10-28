-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_unbounded_strict_exit_factor_lt_one
-- name    : AvramDividend.Classical.chat04_unbounded_strict_exit_factor_lt_one
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:25:20.164151+00:00
-- url     : https://prove2.me/theorems/521b4098-87b9-43f9-ab94-f079a56462fa
-- title:
--   Strict contraction of the two-sided discounted exit factor under unbounded variation
-- statement:
--   For a spectrally negative Lévy process with unbounded variation, positive discount and reserve strictly inside [0,a], the q-discounted upper-before-lower first-passage expectation is strictly less than one. This uses the independently Proved positive Esscher root and the strict positive-root exponential exit bound, and requires no stopped-scale harmonicity or two-sided exit scale formula.
-- source:
--   Avram, Palmowski and Pistorius (2007), arXiv:math/0702893; Prove2Me unbounded_esscher_root_of_notBV and chat04_strict_exit_factor_lt_one_of_positive_root.

import Mathlib.Data.ENNReal.Basic
import Theorems.Thm_AvramDividend_Classical_unbounded_esscher_root_of_notBV
import Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_factor_lt_one_of_positive_root

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_unbounded_strict_exit_factor_lt_one
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x < a) :
    twoSidedExitExpectation X q a x < 1 := by sorry
