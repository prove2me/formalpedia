-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb_obstruction_original_linear_dividendMeasure_interval_mass
-- name    : AvramDividend.Classical.avram_bvb_obstruction_original_linear_dividendMeasure_interval_mass
-- status  : Disproved
-- author  : @WillR
-- created : 2026-11-15T07:24:59.542236+00:00
-- url     : https://prove2.me/theorems/bb518165-65c2-4ac2-9b41-c2a28236cf97
-- title:
--   Original dividend Stieltjes measure of any local unit-linear path has exact interval mass
-- statement:
--   For any original admissible dividend strategy whose cash path equals D(t)=t throughout [0,T], the actual original Stieltjes dividendMeasure gives mass t on every interval (0,t] with t≤T. This is a source-exact bridge from zero-barrier linear no-jump paths to the discounted dividend cash limit and a positive-cap pathwise obstruction.
-- source:
--   Unfold original dividendMeasure as the Stieltjes measure induced by the globally monotone dividend strategy. Use the pinned StieltjesFunction.measure_Ioc identity and exact D(0)=0, D(t)=t. No replacement of original dividendMeasure or paymentTimes.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open Classical MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_bvb_obstruction_original_linear_dividendMeasure_interval_mass
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T t : ℝ≥0)
    (ht : t ≤ T)
    (hLinear : ∀ s : ℝ≥0, s ≤ T → D s ω = (s : ℝ)) :
    dividendMeasure D ω (Ioc (0 : ℝ) (t : ℝ)) =
      ENNReal.ofReal (t : ℝ) := by sorry
