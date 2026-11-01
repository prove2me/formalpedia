-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
-- name    : AvramDividend.Classical.avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-31T20:22:37.145937+00:00
-- url     : https://prove2.me/theorems/28fa6c0e-00ee-4938-a1f1-df9a1b19ad53
-- title:
--   Complete weighted Stieltjes closed interval equals time-zero right atom plus all positive-time mass
-- statement:
--   For every original adapted monotone left-continuous dividend strategy D, each path, every finite horizon T≥0 and arbitrary nonnegative extended-real weight f, the entire closed-horizon Stieltjes integral on [0,T] equals the exact time-zero right atom D_{0+} times f(0), plus the full positive-time (0,T] Stieltjes integral. No atom concentration assumption is made: diffuse and singular-continuous mass remains wholly in the second term. This permits converting the new same-source expected closed-horizon exponential cash budget into an actual Icc dividendMeasure integral.
-- source:
--   Pinned Mathlib lintegral_union and lintegral_singleton; Proved original dividendMeasure_singleton_eq_rightLimit_sub; exact initial D0=0.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_singleton_eq_rightLimit_sub
open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave4_03_dividendMeasure_Icc_weighted_zeroAtom_plus_Ioc
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {𝓕 : Filtration ℝ≥0 mΩ}
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (f : ℝ → ℝ≥0∞) :
    (∫⁻ s in Icc (0 : ℝ) (T : ℝ), f s ∂dividendMeasure D ω) =
    ENNReal.ofReal (rightLimit D 0 ω) * f 0 +
      (∫⁻ s in Ioc (0 : ℝ) (T : ℝ), f s ∂dividendMeasure D ω) := by sorry
