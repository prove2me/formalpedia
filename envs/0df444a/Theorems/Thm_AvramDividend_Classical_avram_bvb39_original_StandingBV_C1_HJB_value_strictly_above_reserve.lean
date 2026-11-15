-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bvb39_original_StandingBV_C1_HJB_value_strictly_above_reserve
-- name    : AvramDividend.Classical.avram_bvb39_original_StandingBV_C1_HJB_value_strictly_above_reserve
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T18:23:37.598147+00:00
-- url     : https://prove2.me/theorems/f6400022-beba-4722-988f-3aa3c0ffc592
-- title:
--   Original Standing bounded-variation finitecap candidate HJB supersolution strictly dominates controlled reserve on closed band
-- statement:
--   For the original Standing bounded-variation spectrally negative Lévy process and candidate w satisfying the true HJB, w(0)≥0, finite positive reserve cap C, and derivative w′≥1 on (0,C), prove the stringent source consequence w(y)>y for every reserve 0≤y≤C, including zero and upper cap. This follows from Proved standing BV positivity w(0)>0 (786bca56) and Proved original finite-cap affine secant (849da3fc). Supports positivity of the original controlled prepayment terminal at every admissible in-band reserve and helps remove redundant stopped-value assumptions.
-- source:
--   Proved 786bca56 origin positivity under Standing BV HJB and Proved 849da3fc global finite-cap C1 secant; no new regularity.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open Classical MeasureTheory Filter Set AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_bvb39_original_StandingBV_C1_HJB_value_strictly_above_reserve
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hStanding : X.Standing) (hBV : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (w : ℝ → ℝ) (C : ℝ≥0∞) (hC : 0 < C)
    (hFinite : C ≠ ⊤)
    (hwCont : ContinuousOn w (Ici 0)) (hw0 : 0 ≤ w 0)
    (hwNeg : ∀ y : ℝ, y < 0 → w y = 0)
    (hwSmooth : ContDiffOn ℝ 1 w
      {y : ℝ | 0 < y ∧ ENNReal.ofReal y < C})
    (hwGen : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      X.GeneratorIntegrable w y ∧ X.generator w y - q * w y ≤ 0)
    (hwGrad : ∀ y : ℝ, 0 < y → ENNReal.ofReal y < C →
      1 ≤ deriv w y) :
    ∀ y : ℝ, 0 ≤ y → y ≤ C.toReal → y < w y := by sorry
