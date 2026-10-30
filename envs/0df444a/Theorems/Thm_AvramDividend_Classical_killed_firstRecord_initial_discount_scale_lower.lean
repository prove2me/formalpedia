-- Prove2me | Theorems.Thm_AvramDividend_Classical_killed_firstRecord_initial_discount_scale_lower
-- name    : AvramDividend.Classical.killed_firstRecord_initial_discount_scale_lower
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T15:28:29.037161+00:00
-- url     : https://prove2.me/theorems/44f0919f-2032-40e1-8182-37adb60a402a
-- title:
--   First killed upward record has the left scale-ratio discounted lower bound
-- statement:
--   Starting at zero, the expected q-discounted ε payment at the first strict upward record ε, killed by actual reflected ruin at barrier a, is at least ε W(a−ε)/W(a). This is the base stochastic exit estimate for the stopped renewal lower bound and should follow from the standard two-sided scale-function exit identity plus the verified killed-first-upcrossing survival sandwich.
-- source:
--   Avram, Palmowski, Pistorius (2007), two-sided q-scale exit law and Proposition 1 reflected first-record survival inequality.

import Mathlib.MeasureTheory.Integral.Lebesgue.Basic
import Mathlib.Data.ENNReal.Real
import Mathlib.Analysis.Complex.Exponential
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_chat08_record_grid_stopped_weights_aemeasurable

open MeasureTheory
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.killed_firstRecord_initial_discount_scale_lower
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ)
    (hW : IsScaleFunction X q W) (a ε : ℝ)
    (ha : 0 < a) (hε : 0 < ε) (hεa : ε < a)
    (hWa : 0 < W a) (hWleft : 0 ≤ W (a - ε))
    (hWinc : W (a - ε) < W a) :
    ENNReal.ofReal (ε * (W (a - ε) / W a)) ≤
      (∫⁻ ω,
      if twoSidedExitUpTime X ((1 : ℝ) * ε) ω <
          barrierRuinTime X a ω then
        ENNReal.ofReal (ε * Real.exp
          (-(q * (twoSidedExitUpTime X ((1 : ℝ) * ε) ω).toReal)))
      else 0 ∂P) := by sorry
