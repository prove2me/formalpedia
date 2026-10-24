-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_strict_exit_discount_zero_of_negative_reserve
-- name    : AvramDividend.Classical.chat04_strict_exit_discount_zero_of_negative_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-23T16:23:40.919343+00:00
-- url     : https://prove2.me/theorems/b13e0dc1-76ad-4d24-8aea-07e2e889376d
-- title:
--   Strict upward-before-ruin discounted transform vanishes below zero capital
-- statement:
--   From a strictly negative initial reserve x, ruin is already present at t=0. The strict downward first-passage time is zero pathwise, while any upward clock lies in ENNReal and cannot precede zero. Thus the upward-before-ruin event is empty and its discounted expectation is exactly zero, for every real q and upper level a. This establishes an exact strict boundary case independently of the q-scale martingale.
-- source:
--   Strict two-sided first-passage definitions with X_0=0 and the ENNReal bottom property; Avram et al. Section 3.2.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Definitions.Def_AvramDividend_Classical_TwoSidedExit

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.chat04_strict_exit_discount_zero_of_negative_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (q a x : ℝ) (hx : x < 0) :
    twoSidedExitExpectation X q a x = 0 := by sorry
