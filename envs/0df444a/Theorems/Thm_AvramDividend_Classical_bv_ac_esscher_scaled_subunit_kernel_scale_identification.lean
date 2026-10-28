-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_scaled_subunit_kernel_scale_identification
-- name    : AvramDividend.Classical.bv_ac_esscher_scaled_subunit_kernel_scale_identification
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T07:45:04.783757+00:00
-- url     : https://prove2.me/theorems/1ca4a724-85b7-48bf-bae4-37890ef7055b
-- title:
--   Esscher scaled renewal kernel identification with the bounded-variation drift multiplier
-- statement:
--   Under standing BV spectrally negative Levy assumptions with an absolutely continuous Levy measure, construct the positive Esscher root and a positive subunit causal renewal kernel. The Esscher-normalised scale function is the primitive of a renewal series multiplied by an independent positive coefficient b, representing the drift-dependent normalisation. This is the exact missing stochastic lemma for the existing correctly scaled parent bv_ac_esscher_scaled_renewal_kernel_series_data. All deterministic convolution bounds are imported from the already Proved causal_subunit_renewal_full_real_power_package.
-- source:
--   Kuznetsov, Kyprianou and Rivero (2013), The Theory of Scale Functions for Spectrally Negative Lévy Processes, bounded-variation renewal equation f=δW and g=δ⁻¹ integrated Lévy tail, Section 3.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_scaled_subunit_kernel_scale_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < ρ ∧ ρ < 1 ∧ 0 < b ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      AntitoneOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ x : ℝ, 0 ≤ x → 0 ≤ κ x) ∧
      IntegrableOn κ (Ioi (0 : ℝ)) volume ∧
      (∫ t in Ioi (0 : ℝ), κ t ∂volume) = ρ ∧
      (∀ F : ℕ → ℝ → ℝ,
        F 0 = κ →
        (∀ n : ℕ, F (n + 1) =
          fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) →
        (∀ x : ℝ, 0 < x →
          IntervalIntegrable
            (fun y : ℝ => b * ∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
        (∀ x : ℝ, 0 < x →
          Real.exp (-(φ * x)) * W x =
            c + ∫ y in (0 : ℝ)..x,
              (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y))) := by sorry
