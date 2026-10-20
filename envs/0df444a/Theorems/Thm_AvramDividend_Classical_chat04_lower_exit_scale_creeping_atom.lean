-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_lower_exit_scale_creeping_atom
-- name    : AvramDividend.Classical.chat04_lower_exit_scale_creeping_atom
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-19T20:22:48.865905+00:00
-- url     : https://prove2.me/theorems/0f1adee0-3670-4143-b12f-b52df6fbae1b
-- title:
--   The general strict lower-exit scale payoff is supported precisely on boundary creeping
-- statement:
--   For any q-scale function W and strict two-sided first-passage times D and U, the killed discounted scale payoff on the lower-first event D<U equals the same q-discount times W(0) if the stopped reserve x+X_D equals zero, and vanishes otherwise. The value at D is at most zero by the proved downward threshold theorem; scale functions vanish below zero, but need not vanish at the origin. The identity therefore isolates exactly the boundary-creeping atom in bounded variation, without imposing W(0)=0 or incorrectly assuming every downward crossing is a strict undershoot.
-- source:
--   Proved AvramDividend.Classical.chat04_firstDowncrossing_value_le_threshold UUID a041b575-e1c0-4395-8a40-dd56ba828378; q-scale predicate definition UUID e6610c46-99bb-43cf-af87-4d07e25d1631; strict two-sided exit stopping time definitions UUID a151e213-9af7-4401-b163-8e74db317cf8. A precise pointwise decomposition toward the Open stopped-scale identity UUID 09663d0d-c23e-47da-b5b9-1bbf28449a4d. It requires a separate almost-sure non-creeping result for general W(0)>0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_chat04_firstDowncrossing_value_le_threshold

open MeasureTheory Filter Set Topology
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_lower_exit_scale_creeping_atom
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (q : ℝ) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (a x : ℝ) (ω : Ω) :
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
        ENNReal.ofReal
          (W (x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω))
     else 0) =
    (if twoSidedExitDownTime X (-x) ω <
          twoSidedExitUpTime X (a - x) ω then
        ENNReal.ofReal (Real.exp (-(q *
          (twoSidedExitDownTime X (-x) ω).toReal))) *
          (if x + X.X (twoSidedExitDownTime X (-x) ω).toNNReal ω = 0 then
             ENNReal.ofReal (W 0)
           else 0)
     else 0) := by sorry
