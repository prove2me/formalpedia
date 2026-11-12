-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a06_finite_real_measures_eq_of_Ioi
-- name    : AvramDividend.Classical.avram_a06_finite_real_measures_eq_of_Ioi
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T14:48:01.451698+00:00
-- url     : https://prove2.me/theorems/c683ea12-c289-49c7-b59c-d7e715494827
-- title:
--   Finite real Borel measures coincide when total masses and all upper half-line masses coincide
-- statement:
--   For two finite Borel measures on the real line, equality on every strict upper half-line together with equality of total mass implies equality of measures. Take complements to obtain equality on every lower closed half-line and invoke the pinned Mathlib measure extensionality theorem. This is a small independently reusable step in extending residual-survival rectangle factorisations to full joint laws.

import Mathlib.MeasureTheory.Constructions.BorelSpace.Order
import Mathlib.MeasureTheory.Measure.MeasureSpace
open MeasureTheory Set
noncomputable section

theorem AvramDividend.Classical.avram_a06_finite_real_measures_eq_of_Ioi
    (μ ν : Measure ℝ) [IsFiniteMeasure μ] [IsFiniteMeasure ν]
    (hUniv : μ Set.univ = ν Set.univ)
    (hIoi : ∀ a : ℝ, μ (Set.Ioi a) = ν (Set.Ioi a)) :
    μ = ν := by sorry
