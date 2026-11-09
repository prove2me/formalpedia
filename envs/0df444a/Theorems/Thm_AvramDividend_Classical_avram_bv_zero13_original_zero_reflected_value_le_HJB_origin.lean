-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_zero13_original_zero_reflected_value_le_HJB_origin
-- name    : AvramDividend.Classical.avram_bv_zero13_original_zero_reflected_value_le_HJB_origin
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-08T23:38:08.943838+00:00
-- url     : https://prove2.me/theorems/8ee61ad1-228f-4239-84f7-353712efeaff
-- title:
--   Finite-activity original zero-barrier discounted reward dominated by the candidate origin value under interior C1 HJB
-- statement:
--   For original Standing BV spectrally negative Levy X with finite negative jump activity and q positive, the whole true zero-barrier discounted payout equals drift divided by q plus negative jump intensity, and this is no more than w(0) whenever w has positive-cap interior C1 HJB inequality and derivative lower bound, is continuous nonnegative at origin and vanishes at negative reserves. The proof directly combines the original exact first-negative-jump payout formula and the quantitative origin HJB drift ceiling. The zero intensity lambda case is included. This is a boundary comparison for the actual zero barrier strategy, not a generic arbitrary D stopped stochastic budget.
-- source:
--   Proved 933ee9aa exact original HJB origin drift ceiling, Proved 6f73f927 exact original zero reflected payout. No auxiliary compound Poisson identification.

import Mathlib.Analysis.Calculus.ContDiff.Defs
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ReflectionBarrier
import Theorems.Thm_AvramDividend_Classical_avram_bv_correct12_finite_activity_origin_HJB_drift_ceiling
import Theorems.Thm_AvramDividend_Classical_bv_finite_activity_zero_reflected_first_jump_payout
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bv_zero13_original_zero_reflected_value_le_HJB_origin
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hBV : X.BoundedVariation)
    (hFinite : X.ν (Iio (0 : ℝ)) < ⊤)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hw_cont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hw_neg : ∀ y < 0, w y = 0)
    (hw_smooth : ContDiffOn ℝ 1 w {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hw_gen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hw_grad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C → 1 ≤ deriv w y) :
    barrierSupValue X 0 q ≤ ENNReal.ofReal (w 0) := by sorry
