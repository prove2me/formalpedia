-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_cumulative_laplace_representation_of_gaussian
-- name    : AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_gaussian
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T15:15:06.711988+00:00
-- url     : https://prove2.me/theorems/d2e374c7-7205-4bad-b995-ed4a55013550
-- title:
--   Unbounded tilted cumulative representation with positive Gaussian coefficient
-- statement:
--   In the unbounded-variation branch with a positive Gaussian coefficient, construct the positive cumulative ladder-potential measure whose Laplace transform matches the Esscher-normalised q-scale function. Gaussian drift in the descending ladder-height subordinator gives the continuous potential near zero and finite positive cumulative mass required by the generic full-support Laplace-identification bridge.
-- source:
--   Wiener-Hopf / descending ladder-height potential representation for spectrally negative Levy processes; Gaussian branch of the unbounded representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_gaussian
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hσ : 0 < X.σ) :
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
