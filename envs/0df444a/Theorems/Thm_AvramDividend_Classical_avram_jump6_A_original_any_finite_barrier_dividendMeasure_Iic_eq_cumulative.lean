-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_any_finite_barrier_dividendMeasure_Iic_eq_cumulative
-- name    : AvramDividend.Classical.avram_jump6_A_original_any_finite_barrier_dividendMeasure_Iic_eq_cumulative
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T11:33:46.202763+00:00
-- url     : https://prove2.me/theorems/6b2ed43a-35a7-4601-9fbe-dccf4a33ca06
-- title:
--   True original capped barrier Stieltjes dividend mass through any time equals cumulative barrier payments for every x≤a
-- statement:
--   For any original spectrally negative Lévy barrier strategy starting at or below its finite barrier, the true Stieltjes dividendMeasure mass on the complete right-closed time interval (-∞,T] equals the actual cumulative barrierStrategy payment D_T, at every physical clock T. The zero mass on negative times follows from D0=0, and the measure of Iic is determined by the monotone Stieltjes function right-limit and limit at -∞. Generalises the existing Proved equal-cap special case 0a41e763 using publicly Proved general barrier monotonicity, right continuity, and the exact rightLimit-comp-toNNReal interface. This removes the unnecessary assumption that the path has a finite future upper-barrier upcrossing when proving zero discounted cash on an early Brownian tube.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
set_option autoImplicit false
open MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_any_finite_barrier_dividendMeasure_Iic_eq_cumulative
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x a : ℝ) (hxa : x ≤ a) (ω : Ω) (T : ℝ≥0) :
    dividendMeasure (barrierStrategy X x a) ω (Iic (T : ℝ)) =
      ENNReal.ofReal (barrierStrategy X x a T ω) := by sorry
