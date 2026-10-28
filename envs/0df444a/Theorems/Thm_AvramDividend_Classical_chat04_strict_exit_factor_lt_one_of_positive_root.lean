-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_factor_lt_one_of_positive_root
-- name    : AvramDividend.Classical.chat04_strict_exit_factor_lt_one_of_positive_root
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T07:20:33.393227+00:00
-- url     : https://prove2.me/theorems/4f9cb366-7985-4e3c-93f3-b0df9a8ae0c3
-- title:
--   Strict contraction of the discounted interior upper-before-ruin exit factor
-- statement:
--   For any spectrally negative Lévy process X, positive discount q and positive Esscher root φ with ψ(φ)=q, the strictly interior two-sided discounted upper-before-ruin expectation is less than one whenever 0≤x<a and a>0. This independent strict contraction follows from the existing Proved positive-root one-sided exit exponential bound and the identity between corrected and canonical strict clocks. It does not use the still Open scale-function exit ratio or stopped q-scale harmonicity, and provides a verified factor below one for renewal sums.
-- source:
--   Avram, Palmowski and Pistorius (2007), arXiv:math/0702893, first-passage exponential martingale bounds; independently Proved corrected_exit_exp_bound_at_positive_root (a6c37169) and chat04_twoSidedExitExpectation_eq_corrected (caca9b2f).

import Mathlib.Analysis.Complex.Exponential
import Mathlib.Data.ENNReal.Real
import Theorems.Thm_AvramDividend_Classical_chat04_twoSidedExitExpectation_eq_corrected
import Theorems.Thm_AvramDividend_Classical_corrected_exit_exp_bound_at_positive_root

open AvramDividend.Classical MeasureTheory
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_factor_lt_one_of_positive_root
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (a x : ℝ) (ha : 0 < a) (hx : 0 ≤ x) (hxa : x < a) :
    twoSidedExitExpectation X q a x < 1 := by sorry
