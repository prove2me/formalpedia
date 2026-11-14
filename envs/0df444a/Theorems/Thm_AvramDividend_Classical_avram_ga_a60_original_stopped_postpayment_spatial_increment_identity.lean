-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_a60_original_stopped_postpayment_spatial_increment_identity
-- name    : AvramDividend.Classical.avram_ga_a60_original_stopped_postpayment_spatial_increment_identity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-12T21:36:11.45519+00:00
-- url     : https://prove2.me/theorems/ba6a5d76-64b4-4df8-98c1-46cb34152859
-- title:
--   Original stopped Gaussian frozen-dividend spatial displacement equals the LÃ©vy increment exactly
-- statement:
--   On the exact clipped stopping grid n/(m+1) of the original spectrally negative Levy process X, the postpayment spatial Taylor increment freezes rightLimit D at the left endpoint. The displaced reserve Z minus Y is exactly the original X.X increment over the stopped cell. This is a pointwise source identification including the single crossing cell and all saturated zero-width cells. It supplies the direct pathwise source identity needed for C2 remainder and moment estimates, without auxiliary process or dividend substitution.
-- source:
--   Original b0d9951c spatial Gaussian interior positive L1 and proved a59 e86b6d78 pathwise C2 lemma.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
open MeasureTheory AvramDividend.Classical
open scoped NNReal
noncomputable section

theorem AvramDividend.Classical.avram_ga_a60_original_stopped_postpayment_spatial_increment_identity
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 -> Ω -> ℝ)
    (n m i : Nat) (ρ : Ω -> ℝ≥0) (ω : Ω) :
    let Δ : ℝ≥0 := (n : ℝ≥0) / ((m : ℝ≥0) + 1)
    let v : Nat -> ℝ≥0 := fun k => min ((k : ℝ≥0) * Δ) (ρ ω)
    let Y : ℝ := x + X.X (v i) ω - rightLimit D (v i) ω
    let Z : ℝ := x + X.X (v (i + 1)) ω - rightLimit D (v i) ω
    Z - Y = X.X (v (i + 1)) ω - X.X (v i) ω := by sorry
