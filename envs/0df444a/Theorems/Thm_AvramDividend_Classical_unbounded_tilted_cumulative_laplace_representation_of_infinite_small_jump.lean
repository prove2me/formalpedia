-- Prove2me | Theorems.Thm_AvramDividend_Classical_unbounded_tilted_cumulative_laplace_representation_of_infinite_small_jump
-- name    : AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_infinite_small_jump
-- status  : Open
-- author  : @WillR
-- created : 2026-10-07T15:15:18.641004+00:00
-- url     : https://prove2.me/theorems/eec8f705-e437-45bb-af25-990c448c46f2
-- title:
--   Unbounded tilted cumulative representation with infinite small-jump first moment
-- statement:
--   In the pure-jump unbounded-variation branch with infinite first absolute small-jump moment, construct the positive cumulative ladder-potential measure whose Laplace transform matches the Esscher-normalised q-scale function. The infinite-activity ladder-height kernel gives positive cumulative mass at every positive reserve without a zero atom.
-- source:
--   Wiener-Hopf / descending ladder-height potential representation for spectrally negative Levy processes; infinite-small-jump branch of the unbounded representation.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_ScaleFunction
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.unbounded_tilted_cumulative_laplace_representation_of_infinite_small_jump
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (q : ℝ) (hq : 0 < q)
    (W : ℝ → ℝ) (hW : IsScaleFunction X q W)
    (hvar : (∫⁻ y in Ioo (-1 : ℝ) 0, ENNReal.ofReal |y| ∂X.ν) = ⊤) :
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
