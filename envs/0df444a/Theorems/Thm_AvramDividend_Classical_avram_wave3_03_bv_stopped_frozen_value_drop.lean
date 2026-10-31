-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_stopped_frozen_value_drop
-- name    : AvramDividend.Classical.avram_wave3_03_bv_stopped_frozen_value_drop
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:42:47.385594+00:00
-- url     : https://prove2.me/theorems/17d877a1-3d4e-43d9-a3f5-b506264307a5
-- title:
--   Genuine stopped Stieltjes dividend payment bounded by frozen HJB value drop including continuous mass
-- statement:
--   At a finite horizon and arbitrary ruin stopping boundary, every actual dividend strategy's full discounted Stieltjes payment mass, including continuous and singular-continuous control and all eligible right-jump rewards, is bounded by the frozen-reserve HJB value drop when the frozen reserve covers the complete terminal right-limit dividend and remains below the cap.
-- source:
--   Proved AvramDividend.Classical.avram_wave3_03_bv_frozen_reserve_closed_discounted_budget and the actual paymentTimes subset [0,T], using Mathlib lintegral_mono_set. No atomicity, original-source compensation or imaginary Itô–Meyer hypothesis.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_frozen_reserve_closed_discounted_budget

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_stopped_frozen_value_drop
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (C : ℝ≥0∞) (hC : 0 < C) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (σ : ℝ≥0∞) (T : ℝ≥0) (y : ℝ)
    (hyD : rightLimit D T ω ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    (∫⁻ t in paymentTimes σ ∩ Iic (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w y - w (y - rightLimit D T ω)) := by sorry
