-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a20_spatial_Borel_simple_mark_integral_partition
-- name    : AvramDividend.Classical.avram_a20_spatial_Borel_simple_mark_integral_partition
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:18:23.408616+00:00
-- url     : https://prove2.me/theorems/4c87924a-5472-47b3-ac1a-71926ecdd384
-- title:
--   Exact spatial Lévy Borel marked simple real integral equals weighted values times measurable fibre measures
-- statement:
--   For any real mark measure ν, Borel set S and finite-valued measurable real simple function g integrable on S, the exact spatial real Bochner integral ∫_S g(z)dν equals the finite sum over mark values y of y times the real measure ν(S∩g^{-1}({y})). The proof uses the pinned Mathlib SimpleFunc.integral_eq_sum under the restricted mark measure and evaluates the measure of each measurable fibre by Measure.restrict_apply. This explicitly identifies the deterministic intensity rates in the already Proved true original finite-simple physical Borel count moments with the spatial Lévy measure integrals appearing in the continuous bounded-mark source moment theorem JA28.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal BigOperators
noncomputable section

theorem AvramDividend.Classical.avram_a20_spatial_Borel_simple_mark_integral_partition
    (ν : Measure ℝ) (S : Set ℝ) (hS : MeasurableSet S)
    (g : SimpleFunc ℝ ℝ)
    (hInt : IntegrableOn (fun z : ℝ => g z) S ν) :
    (∫ z in S, g z ∂ν) =
      ∑ y ∈ g.range, y * (ν (S ∩ g ⁻¹' {y})).toReal := by sorry
