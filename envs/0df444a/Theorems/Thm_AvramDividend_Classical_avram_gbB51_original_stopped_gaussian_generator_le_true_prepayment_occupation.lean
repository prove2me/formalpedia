-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB51_original_stopped_gaussian_generator_le_true_prepayment_occupation
-- name    : AvramDividend.Classical.avram_gbB51_original_stopped_gaussian_generator_le_true_prepayment_occupation
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T17:17:14.03637+00:00
-- url     : https://prove2.me/theorems/bf18e778-4102-4398-9c46-08de9e1c4843
-- title:
--   Original stopped Gaussian caplinear generator drift bounded by true prepayment occupied strip cost on the same physical stopping mask
-- statement:
--   On the genuine stopped physical-time set before the original clock, the Gaussian cap-linear HJB generator drift is at most the upper-strip charge calculated from the actual prepayment riskProcess. This transfers B41 generator drift through the genuine right-limit D versus D comparison, preserving the original controlled process. Integrability of all three original time sources is explicit.
-- source:
--   Proved B41 original postpayment caplinear Gaussian generator HJB integral bound and B49 pointwise original postpaid to prepaid strip indicator. Integral monotonicity transfers occupation cost on the exact same restricted stopped time measure.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_gbB41_original_strict_clock_gaussian_caplinear_occupation_drift_envelope
import Theorems.Thm_AvramDividend_Classical_avram_gbB49_original_postpaid_upper_strip_indicator_le_true_prepaid
import Theorems.Thm_AvramDividend_Classical_dividendStrategy_le_rightLimit
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_gbB51_original_stopped_gaussian_generator_le_true_prepayment_occupation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hν : X.ν = 0)
    (x b : ℝ) (D : ℝ≥0 → Ω → ℝ)
    (hD : IsDividendStrategy 𝓕 D)
    (n : ℕ) (ρ : Ω → ℝ≥0)
    (δ : ℝ) (hδ : 0 < δ)
    (hFloor : ∀ ω t, 0 < t → t < ρ ω →
      δ ≤ riskProcess X x D t ω)
    (w : ℝ → ℝ) (q : ℝ) (hq : 0 ≤ q) (hwb : 0 ≤ w b)
    (hHJB : ∀ y : ℝ, 0 < y → y < b →
      X.generator w y - q * w y ≤ 0) :
    ∀ᵐ ω ∂P,
      let S : Set ℝ := {t : ℝ |
        0 < t ∧ t < (n : ℝ) ∧ t < (ρ ω : ℝ)}
      let Y : ℝ → ℝ := fun t =>
        x + X.X (Real.toNNReal t) ω - rightLimit D (Real.toNNReal t) ω
      let V : ℝ → ℝ := fun z =>
        if z ≤ b then w z else w b + (z - b)
      Integrable (fun t => X.generator V (Y t) - q * V (Y t))
        (volume.restrict S) →
      Integrable (fun t => if b < Y t then max X.c 0 else 0)
        (volume.restrict S) →
      Integrable (fun t =>
        if b < riskProcess X x D (Real.toNNReal t) ω
        then max X.c 0 else 0)
        (volume.restrict S) →
      (∫ t, X.generator V (Y t) - q * V (Y t) ∂(volume.restrict S)) ≤
        (∫ t, if b < riskProcess X x D (Real.toNNReal t) ω
          then max X.c 0 else 0 ∂(volume.restrict S)) := by sorry
