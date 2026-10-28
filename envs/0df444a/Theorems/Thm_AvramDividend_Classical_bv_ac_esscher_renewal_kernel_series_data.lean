-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_ac_esscher_renewal_kernel_series_data
-- name    : AvramDividend.Classical.bv_ac_esscher_renewal_kernel_series_data
-- status  : Open
-- author  : @WillR
-- created : 2026-10-24T17:10:03.75037+00:00
-- url     : https://prove2.me/theorems/fa263a12-4366-44a0-a018-5ff83c0799be
-- title:
--   Esscher bounded-variation renewal kernel and series representation data
-- statement:
--   For BV spectral negativity and absolutely continuous Lévy measure under standing assumptions, construct a positive Esscher root, a causal integrable continuous renewal kernel, a subcritical contraction parameter and its nonnegative convolution-power series. Prove the pointwise geometric bound, interval integrability and Laplace-identified equality of the tilted q-scale function with a constant plus the integrated series. Continuity of the series is factored out into the already Proved causal_renewal_density_continuous_of_convolution_bounds, which gives the precise parent bv_ac_esscher_continuous_renewal_density_representation. This captures the remaining probabilistic kernel and uniqueness obligations.
-- source:
--   Spectrally negative BV Lévy-Khintchine Esscher factorisation ψ(φ+s)-ψ(φ)=s[d-ℒκ(s)] and renewal Neumann series; proven generic causal convolution-power bounds and positive Laplace identities.

import Mathlib.MeasureTheory.Integral.IntervalIntegral.FundThmCalculus
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction

open AvramDividend.Classical MeasureTheory Set intervalIntegral
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_ac_esscher_renewal_kernel_series_data
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) (hac : X.ν ≪ volume) :
    ∃ (φ c ρ : ℝ) (κ : ℝ → ℝ) (F : ℕ → ℝ → ℝ),
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
          (fun y : ℝ => ∑' n : ℕ,
            if n = 0 then (0 : ℝ) else F (n - 1) y) volume 0 x) ∧
      (∀ x : ℝ, 0 < x →
        Real.exp (-(φ * x)) * W x =
          c + ∫ y in (0 : ℝ)..x,
            (∑' n : ℕ, if n = 0 then (0 : ℝ) else F (n - 1) y)) := by sorry
