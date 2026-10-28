-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_renewal_kernel_series_data_with_pointwise
-- name    : AvramDividend.Classical.bv_esscher_scaled_renewal_kernel_series_data_with_pointwise
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T10:42:50.525997+00:00
-- url     : https://prove2.me/theorems/7d7b2e94-4ccb-4049-8d33-225aae3b20da
-- title:
--   BV Esscher real renewal powers and scale primitive with exact canonical kernel
-- statement:
--   Construct the full positive subcritical Esscher real convolution-power sequence, its summability estimates, its integrated scale primitive, and preserve the exact pointwise strict-tail kernel formula, for general bounded-variation spectrally negative Lévy processes without jump-measure absolute continuity.
-- source:
--   Source-derived strengthening of previously Proved bv_ac_esscher_scaled_renewal_kernel_series_data, accepted source SHA-256 ee713fed0a16d274ec70778fb2e29a7e1fd11310a1829c6bedd15d8ac196c296. Depends on separately authored scaled primitive with pointwise kernel.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
import Theorems.Thm_AvramDividend_Classical_bv_esscher_scaled_subunit_kernel_scale_identification_with_pointwise
import Theorems.Thm_AvramDividend_Classical_causal_subunit_renewal_full_real_power_package
open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_scaled_renewal_kernel_series_data_with_pointwise
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
      (∀ t : ℝ, κ t =
        if 0 < t then
          ENNReal.toReal (((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 => ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) / X.drift else 0) ∧
      0 < φ ∧ X.ψ φ = q ∧
      0 < ρ ∧ ρ < 1 ∧
      Integrable κ volume ∧
      ContinuousOn κ (Ioi (0 : ℝ)) ∧
      (∀ x : ℝ, x ≤ 0 → κ x = 0) ∧
      (∀ ε : ℝ, 0 < ε → ∃ M : ℝ, ∀ x : ℝ, ε ≤ x → |κ x| ≤ M) ∧
      F 0 = κ ∧
      (∀ n : ℕ, F (n + 1) =
        fun x : ℝ => ∫ y : ℝ, κ y * F n (x - y) ∂volume) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 ≤ x → 0 ≤ F n x) ∧
      (∀ n : ℕ, ∀ x : ℝ, 0 < x →
        F n x ≤ ((n + 1 : ℝ) ^ 2 * ρ ^ (n + 1)) / x) ∧
      (∀ x : ℝ, 0 < x →
        IntervalIntegrable
          (fun y : ℝ => b * ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x,
            (b * ∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y)) := by sorry
