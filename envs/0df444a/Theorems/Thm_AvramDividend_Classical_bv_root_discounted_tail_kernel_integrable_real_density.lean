-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_integrable_real_density
-- name    : AvramDividend.Classical.bv_root_discounted_tail_kernel_integrable_real_density
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T12:03:20.571641+00:00
-- url     : https://prove2.me/theorems/fd704b38-79ef-4b53-960e-01c6dc696ab6
-- title:
--   Integrable nonnegative real-density Esscher BV jump-tail renewal kernel at a positive root
-- statement:
--   Under the BV spectrally negative Lévy standing branch at a positive Esscher root, the canonically constructed discounted jump-tail measure admits a nonnegative measurable and Lebesgue-integrable real density. Preserve the support, subcritical mass and exact positive Laplace transform. This provides the Integrable kernel premise, in addition to the already proved real-density premise, for the correctly normalised geometric renewal data on the cstar finiteness route.
-- source:
--   Canonical Proved bv_root_discounted_tail_kernel_real_density_package and the Mathlib HasFiniteIntegral criterion for nonnegative real functions

import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_real_density_package
import Mathlib.MeasureTheory.Function.L1Space.Integrable
import Mathlib.MeasureTheory.Measure.WithDensity

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_root_discounted_tail_kernel_integrable_real_density
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ) (K : ℝ → ℝ),
      SFinite κ ∧ κ ≪ volume ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      Measurable K ∧ (∀ x : ℝ, 0 ≤ K x) ∧
      Integrable K volume ∧
      κ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by sorry
