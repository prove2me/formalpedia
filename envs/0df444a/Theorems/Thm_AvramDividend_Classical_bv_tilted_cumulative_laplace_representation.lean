-- Prove2me | Theorems.Thm_AvramDividend_Classical_bv_tilted_cumulative_laplace_representation
-- name    : AvramDividend.Classical.bv_tilted_cumulative_laplace_representation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-06T22:29:57.04696+00:00
-- url     : https://prove2.me/theorems/d7edfe09-24dd-415a-9cae-3e2ba4fc6dba
-- title:
--   Bounded-variation Esscher-normalised scale function as cumulative positive renewal measure
-- statement:
--   For a standing spectrally negative Levy process of bounded variation and q>0, there exist phi>0, a locally finite positive measure beta with an atom at zero, and a Laplace half-plane on which the Esscher-normalised scale function exp(-phi*x)*W(x) has the same integral transform as the cumulative function beta((−infinity,x]). The needed integrability is part of the statement. The constructive route uses phi=q/delta for positive drift delta, a nonnegative shifted tail kernel, and a geometric positive convolution renewal measure. This is a genuine model-specific stochastic/analytic proof obligation and allows the existing Proved uniqueness/positive-cumulative theorem to deliver tilted monotonicity.
-- source:
--   Avram, Palmowski and Pistorius (2007), Levy BV scale-function renewal identity; local independent derivation in artifacts/avram-cstar/BV_SHIFTED_POSITIVE_RENEWAL_20261006.md; use the already Proved positive_geometric_renewal_measure_package and positive_tilted_of_laplace_cumulative_identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.bv_tilted_cumulative_laplace_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hbv : X.BoundedVariation) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      0 < β {0} ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by sorry
