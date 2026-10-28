-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_esscher_canonical_tail_measure_package
-- name    : AvramDividend.Classical.bv_esscher_canonical_tail_measure_package
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T21:46:42.089429+00:00
-- url     : https://prove2.me/theorems/e4d49417-4743-46c8-a668-1e7827440696
-- title:
--   Canonical BV Esscher discounted-tail measure with exact root Laplace data
-- statement:
--   Retain the exact positive-axis discounted Lévy jump-tail withDensity measure when proving its subcritical total mass and its Esscher positive Laplace transform. The existing proved AC package only returns an existential measure, obscuring the identity needed to match the explicitly normalised continuous kernel to the geometric renewal witness. This strengthens the accepted construction by preserving that identity.
-- source:
--   Source-adapted accepted proof of bv_root_discounted_tail_kernel_ac_package, UUID 6f0d7e31-2588-4069-b0e6-b3872037a991; Avram, Palmowski and Pistorius (2007), BV renewal scale representation.

import Theorems.Thm_AvramDividend_Classical_bv_esscher_root_subcritical_kernel_mass
import Theorems.Thm_AvramDividend_Classical_esscher_tail_kernel_mass_as_discounted_first_moment
import Theorems.Thm_AvramDividend_Classical_positiveLaplace_esscher_discounted_tail_kernel
import Mathlib.Analysis.Complex.Exponential
import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_esscher_canonical_tail_measure_package
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hbv : X.BoundedVariation)
    (q : ℝ) (hq : 0 < q)
    (φ : ℝ) (hφ : 0 < φ) (hroot : X.ψ φ = q)
    (hδ : 0 < X.drift) :
    ∃ (κ : Measure ℝ),
      κ =
        (volume.restrict (Ioi (0 : ℝ))).withDensity (fun t : ℝ =>
          ((X.ν.map (fun y : ℝ => Real.toNNReal (-y))).withDensity
            (fun z : ℝ≥0 =>
              ENNReal.ofReal (Real.exp (-(φ * (z : ℝ))))))
            {z : ℝ≥0 | t < (z : ℝ)}) ∧
      SFinite κ ∧ κ ≪ volume ∧ κ (Iio (0 : ℝ)) = 0 ∧
      κ Set.univ < ENNReal.ofReal X.drift ∧
      (∀ s : ℝ, 0 < s →
        (∫⁻ x : ℝ, ENNReal.ofReal (Real.exp (-(s * x))) ∂κ) =
          (∫⁻ z : ℝ≥0,
            ENNReal.ofReal (Real.exp (-(φ * (z : ℝ)))) *
              ENNReal.ofReal
                ((1 - Real.exp (-(s * (z : ℝ)))) / s)
              ∂(X.ν.map (fun y : ℝ => Real.toNNReal (-y))))) := by sorry
