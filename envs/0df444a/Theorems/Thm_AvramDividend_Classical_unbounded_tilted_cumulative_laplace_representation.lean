-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_cumulative_laplace_representation
-- name    : AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation
-- status  : Open
-- author  : @WillR
-- created : 2026-10-06T23:16:52.495995+00:00
-- url     : https://prove2.me/theorems/cc8412fd-c4b7-4ad7-bb22-0c63fa2bf6ca
-- title:
--   Unbounded-variation scale function as a positive cumulative ladder-potential Laplace transform
-- statement:
--   Under the canonical standing, q>0, scale-function and unbounded-variation assumptions, construct a positive measure β with strictly positive finite cumulative mass β((−∞,x]) for every x>0 and an exponent φ>0, so that the exponential tilt exp(-φx) W(x) has the same integrable Laplace transform on a right half-plane as the cumulative function β((−∞,x]). No atom at zero is assumed. This precise stochastic statement can be derived from a descending ladder-height potential/Wiener-Hopf representation, splitting into Gaussian and infinite-small-jump cases where needed. It is the one source-specific missing input for the newly proved or submitted generic full-support Laplace identification bridge to discharge the original Open unbounded-variation positivity theorem.
-- source:
--   Kuznetsov, Kyprianou, Rivero (2012), fluctuation identities for q-scale functions; analogous to AvramDividend.Classical.bv_tilted_cumulative_laplace_representation, but no zero atom; new generic positive_tilted_of_laplace_cumulative_identification_full_support.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hnbv : ¬ X.BoundedVariation) :
    ∃ (β : Measure ℝ) (φ b : ℝ),
      0 < φ ∧
      (∀ x : ℝ, β (Iic x) ≠ ⊤) ∧
      (∀ x : ℝ, 0 < x → 0 < β (Iic x)) ∧
      ∀ θ : ℝ, b < θ →
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x)) (Ioi 0) ∧
        IntegrableOn (fun x : ℝ => Real.exp (-θ * x) *
          (β (Iic x)).toReal) (Ioi 0) ∧
        ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
          (Real.exp (-φ * x) * W x) =
          ∫ x in Ioi (0 : ℝ), Real.exp (-θ * x) *
            (β (Iic x)).toReal := by sorry
