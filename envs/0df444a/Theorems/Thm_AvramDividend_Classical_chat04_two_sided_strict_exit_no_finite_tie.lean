-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_two_sided_strict_exit_no_finite_tie
-- name    : AvramDividend.Classical.chat04_two_sided_strict_exit_no_finite_tie
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T19:59:40.948343+00:00
-- url     : https://prove2.me/theorems/0689217e-889b-48f4-953e-8c1e374a42d8
-- title:
--   Separated strict two-sided Lévy first passage times cannot coincide at a finite time
-- statement:
--   For a spectrally negative Lévy process started from zero and two separated thresholds a−x and −x with a>0 and x≤a, let U and D be the infima of the strict upward and strict downward crossing times. If U=D, their common extended time must be infinity. Indeed at a finite common crossing, absence of upward overshoots and right continuity give X_U=a−x, whereas the finite strict downward first-passage theorem gives X_U≤−x, contradicting a>0. This theorem removes finite ties when splitting the strict two-sided stopped-scale payoff into successful upper exit and lower ruin.
-- source:
--   The already Proved AvramDividend.Classical.firstUpcrossing_value_eq_threshold (UUID 014436e7-36d8-45ea-8ca6-bc6917b7788c), the separate downward threshold theorem AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold (UUID a041b575-e1c0-4395-8a40-dd56ba828378), and published strict two-sided stopping-time definitions (UUID a151e213-9af7-4401-b163-8e74db317cf8). No stochastic optional sampling is assumed.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Theorems.Thm_AvramDividend_Classical_firstUpcrossing_value_eq_threshold
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_two_sided_strict_exit_no_finite_tie
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (a x : ℝ) (ha : 0 < a) (hxa : x ≤ a) (ω : Ω) :
    twoSidedExitUpTime X (a - x) ω = twoSidedExitDownTime X (-x) ω →
      twoSidedExitUpTime X (a - x) ω = ⊤ := by sorry
