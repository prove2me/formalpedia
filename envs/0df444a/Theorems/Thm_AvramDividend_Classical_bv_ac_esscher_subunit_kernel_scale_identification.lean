-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_subunit_kernel_scale_identification
-- name    : AvramDividend.Classical.bv_ac_esscher_subunit_kernel_scale_identification
-- status  : Open
-- author  : @WillR
-- created : 2026-10-25T07:37:19.450069+00:00
-- url     : https://prove2.me/theorems/fab50493-c2f0-473e-9b30-03ff886bc119
-- title:
--   Subunit Esscher renewal kernel and scale identity in the bounded-variation atomless branch
-- statement:
--   Under standing bounded variation and absolutely continuous negative Lévy measure, the Esscher-normalised scale function has a positive subunit causal renewal-kernel representation. The kernel is supported on the positive axis, nonnegative, decreasing and integrable, with total mass rho strictly between zero and one. Every recursively defined convolution-power sequence from the kernel yields the stated interval-integrable renewal density whose primitive equals the tilted scale function. This isolates the stochastic kernel identification from deterministic convolution positivity, geometric bounds and local boundedness, which are already proved in causal_subunit_renewal_full_real_power_package and follow from kernel monotonicity. The child enables a one-open-child reduction of bv_ac_esscher_renewal_kernel_series_data (fa263a12-4366-44a0-a018-5ff83c0799be) with no reverse dependency.
-- source:
--   Chan, Kyprianou and Savov (2011), smoothness and renewal-density construction for bounded-variation processes, combined with Kuznetsov, Kyprianou and Rivero (2012), Esscher change and renewal measure.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_subunit_kernel_scale_identification
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration NNReal mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q) (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c ρ : ℝ) (κ : ℝ → ℝ),
      0 < φ ∧ X.ψ φ = q ∧ 0 < ρ ∧ ρ < 1 ∧
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
            (fun y : ℝ => ∑' n : ℕ,
              if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
        (∀ x : ℝ, 0 < x →
          Real.exp (-(φ * x)) * W x =
            c + ∫ y in (0 : ℝ)..x,
              (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y))) := by sorry
