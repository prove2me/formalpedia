-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_upper_ray_cylinders_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_b_upper_ray_cylinders_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:45:45.405986+00:00
-- url     : https://prove2.me/theorems/92d90ca8-16e2-415c-9133-33a98a9612a4
-- title:
--   Strict upper-ray factorisation determines full independence
-- statement:
--   For a measurable real supremum-type statistic R and measurable terminal drawdown statistic Y under a probability measure, suppose for every level a and every measurable drawdown event B the joint upper-threshold probability P(R>a,Y∈B) factors into P(R>a)P(Y∈B). Then R and Y are independent as random variables. Strict upper half-lines generate the Borel sigma-algebra and form a pi-system, so Mathlib's independence extension yields the complete Borel distributional assertion without assuming Wiener–Hopf independence.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_upper_ray_cylinders_indepFun
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R)
    (Y : Ω → β) (hY : Measurable Y)
    (hTail : ∀ (a : ℝ) (B : Set β), MeasurableSet B →
      P (R ⁻¹' (Ioi a) ∩ Y ⁻¹' B) =
        P (R ⁻¹' (Ioi a)) * P (Y ⁻¹' B)) :
    IndepFun R Y P := by sorry
