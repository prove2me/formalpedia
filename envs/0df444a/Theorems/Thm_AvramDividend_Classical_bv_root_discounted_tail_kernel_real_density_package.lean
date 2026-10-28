-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_real_density_package
-- name    : AvramDividend.Classical.bv_root_discounted_tail_kernel_real_density_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T11:55:26.610924+00:00
-- url     : https://prove2.me/theorems/d89b841d-a606-44ae-a14f-7c6584165d37
-- title:
--   Positive-root bounded-variation Esscher kernel with an explicit nonnegative real density
-- statement:
--   For a spectrally negative bounded-variation Lévy process with strictly positive drift and a positive Esscher root, construct the finite discounted positive jump-tail measure together with a measurable nonnegative real Lebesgue density. Preserve the exact support, subcritical mass, and Laplace-transform identity already established in the Proved BV kernel package. This establishes the real-kernel hypothesis required to apply the geometric renewal density and scale-derivative growth tools on the cstar finiteness path.
-- source:
--   Accepted AvramDividend.Classical.bv_root_discounted_tail_kernel_ac_package and the Radon–Nikodym theorem in pinned Mathlib

import Theorems.Thm_AvramDividend_Classical_bv_root_discounted_tail_kernel_ac_package
import Mathlib.MeasureTheory.Measure.Decomposition.RadonNikodym
import Mathlib.MeasureTheory.Measure.WithDensity
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Data.ENNReal.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_root_discounted_tail_kernel_real_density_package
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
      κ = volume.withDensity (fun x : ℝ => ENNReal.ofReal (K x)) ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by sorry
