-- Prove2me | Theorems.Thm_AvramDividend_Classical_psi_normalised_unbounded_of_unbounded_variation
-- name    : AvramDividend.Classical.psi_normalised_unbounded_of_unbounded_variation
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-25T09:24:22.902696+00:00
-- url     : https://prove2.me/theorems/9f622e05-0375-4204-b9ae-299d3de043f5
-- title:
--   Unbounded variation forces the normalised Lévy exponent to diverge
-- statement:
--   For every spectrally negative Lévy process of unbounded variation and every real C, there is a β≥1 beyond which ψ(θ)/θ > C for every θ≥β. This combines the two exclusive variation mechanisms: a strictly positive Gaussian coefficient or an infinite small negative jump first moment. It supplies a reusable, discount-independent exponent-growth prerequisite for Esscher first-passage and zero-discount scale-function regularity.
-- source:
--   Proved unbounded_variation_gaussian_or_infinite_small_jump_moment (cb0b01e6-6ae4-4fba-affb-24f5e5c449c6); proved gaussian_psi_superlinear_of_positive_sigma (c1392cb2-b5da-4f7e-b8e7-854fe3d2ee4f); proved psi_normalised_unbounded_small_jumps (3fc04011-a4da-4c0d-a8b8-9ac3ecf6a855).

import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.psi_normalised_unbounded_of_unbounded_variation
    {Ω : Type*} [mΩ : MeasurableSpace Ω]
    {P : Measure Ω} {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hnbv : ¬ X.BoundedVariation) :
    ∀ C : ℝ, ∃ β : ℝ, 1 ≤ β ∧
      ∀ θ : ℝ, β ≤ θ → C < X.ψ θ / θ := by sorry
