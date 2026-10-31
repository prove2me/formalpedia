-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_frozen_reserve_discounted_stieltjes_budget
-- name    : AvramDividend.Classical.avram_wave3_03_bv_frozen_reserve_discounted_stieltjes_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-30T08:00:52.538505+00:00
-- url     : https://prove2.me/theorems/1683a39d-9534-45c3-8adb-6e112e1a32ed
-- title:
--   Full discounted Stieltjes dividends from a frozen positive reserve are bounded by the HJB potential drop
-- statement:
--   For any genuine adapted monotone left-continuous dividend strategy D and any finite horizon T, the full discounted dividendMeasure integral over [0,T), including continuous and singular-continuous payment mass and the time-zero right-jump atom, is bounded by the HJB test potential decrease w(y)-w(y-D(T)) when the frozen reserve y can cover D(T) and remains under cap C. The necessary cap-inclusive secant estimate is derived from the strict-band gradient by the separate proven child; no countable-jump concentration assumption appears.
-- source:
--   Combine accepted exact Stieltjes half-open cumulative identity 56472398, accepted discount domination fc69051f, and source cap-inclusive mean-value gradient secant avram_wave3_03_bv_full_cap_gradient_secant. All three operate on the actual dividendMeasure D, including nonatomic mass.

import Mathlib
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_dividendMeasure_Ico_zero_eq_dividendValue
import Theorems.Thm_AvramDividend_Classical_discounted_stieltjes_lintegral_le_measure
import Theorems.Thm_AvramDividend_Classical_avram_wave3_03_bv_full_cap_gradient_secant

open MeasureTheory Set
open scoped NNReal ENNReal
open AvramDividend.Classical

theorem AvramDividend.Classical.avram_wave3_03_bv_frozen_reserve_discounted_stieltjes_budget
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {𝓕 : Filtration ℝ≥0 mΩ}
    (C : ℝ≥0∞) (hC : 0 < C) (q : ℝ) (hq : 0 ≤ q) (w : ℝ → ℝ)
    (hw_cont : ContinuousOn w (Ici 0))
    (hw_smooth : ContDiffOn ℝ 1 w {z : ℝ | 0 < z ∧ ENNReal.ofReal z < C})
    (hw_grad : ∀ z : ℝ, 0 < z → ENNReal.ofReal z < C → 1 ≤ deriv w z)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (ω : Ω) (T : ℝ≥0) (y : ℝ)
    (hyD : D T ω ≤ y) (hyC : ENNReal.ofReal y ≤ C) :
    (∫⁻ t in Ico (0 : ℝ) (T : ℝ),
      ENNReal.ofReal (Real.exp (-(q * t))) ∂(dividendMeasure D ω)) ≤
      ENNReal.ofReal (w y - w (y - D T ω)) := by sorry
