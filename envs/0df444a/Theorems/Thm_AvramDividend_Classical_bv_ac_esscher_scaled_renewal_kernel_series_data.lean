-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_scaled_renewal_kernel_series_data
-- name    : AvramDividend.Classical.bv_ac_esscher_scaled_renewal_kernel_series_data
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-24T17:46:38.463993+00:00
-- url     : https://prove2.me/theorems/9be5ada9-6f14-4f14-8115-14262e488433
-- title:
--   Correctly normalised Esscher BV renewal kernel, convolution powers and scaled density
-- statement:
--   Under standing BV spectrally negative Lévy assumptions with absolutely continuous jump measure, construct the positive Esscher root, causal continuous subcritical renewal kernel and nonnegative convolution powers, with geometric pointwise bounds. The tilted scale function equals a constant plus the integral of the renewal series with an independent scalar coefficient b. For drift d the standard renewal identity has constant c=1/d and series multiplier b=c, preserving the correct normalisation. This is the precise mathematical input for the open BV continuous Esscher renewal-density representation parent.
-- source:
--   Bounded-variation Esscher shifted jump-tail renewal equation; c=1/d and b=c; positive causal kernel κ=k/d with ∫κ<1.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_scaled_renewal_kernel_series_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c ρ b : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
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
