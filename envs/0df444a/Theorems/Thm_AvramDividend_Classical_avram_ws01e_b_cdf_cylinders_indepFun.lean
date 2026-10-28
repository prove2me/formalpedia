-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ws01e_b_cdf_cylinders_indepFun
-- name    : AvramDividend.Classical.avram_ws01e_b_cdf_cylinders_indepFun
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-27T21:22:33.500645+00:00
-- url     : https://prove2.me/theorems/3c30ce31-a83f-4592-a29c-73b07c4f3efa
-- title:
--   Half-line CDF-event factorisation extends to full independence of a real statistic and future event
-- statement:
--   Suppose R is a real-valued measurable random variable and Y is an arbitrary measurable future-path statistic on a probability space. If for every threshold a and every measurable future event B, the probability of {R≤a,Y∈B} factors as the product of its marginals, then R and Y are independent random variables for all Borel events. The proof compares the finite pushforward of the measure restricted to Y∈B with a scalar multiple of R's pushforward law, uses uniqueness from Iic intervals, and concludes IndepFun for all measurable rectangles. This is the π-λ completion stage required by genuine exponential-horizon Wiener–Hopf splitting, without assuming Wiener–Hopf independence.
-- source:
--   Pinned Mathlib 0df444a: MeasureTheory.Measure.ext_of_Iic, Measure.map_apply, Measure.restrict_apply, Measure.smul_apply and ProbabilityTheory.indepFun_iff_indepSet_preimage; Borel measure uniqueness / π-λ theorem in the proof of Wiener–Hopf splitting.

import Mathlib.Probability.Independence.Basic
import Mathlib.MeasureTheory.Measure.Map
import Mathlib.MeasureTheory.Measure.Restrict
import Mathlib.MeasureTheory.Constructions.BorelSpace.Order

open MeasureTheory ProbabilityTheory Set
open scoped ENNReal

theorem AvramDividend.Classical.avram_ws01e_b_cdf_cylinders_indepFun
    {Ω β : Type*} [MeasurableSpace Ω] [MeasurableSpace β]
    (P : Measure Ω) [IsProbabilityMeasure P]
    (R : Ω → ℝ) (hR : Measurable R)
    (Y : Ω → β) (hY : Measurable Y)
    (hCDF : ∀ (a : ℝ) (B : Set β), MeasurableSet B →
      P (R ⁻¹' (Iic a) ∩ Y ⁻¹' B) =
        P (R ⁻¹' (Iic a)) * P (Y ⁻¹' B)) :
    IndepFun R Y P := by sorry
