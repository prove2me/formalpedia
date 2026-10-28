-- Prove2me | Theorems.Thm_AvramDividend_Classical_canonical_poisson_band_zero_law_transfer
-- name    : AvramDividend.Classical.canonical_poisson_band_zero_law_transfer
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T18:43:52.803698+00:00
-- url     : https://prove2.me/theorems/db22d1d5-9099-452d-996f-04046ae1d764
-- title:
--   Measurable canonical finite-band Poisson zero-count laws transfer to the actual spectrally negative Lévy path through matching exponents
-- statement:
--   Let X and Y be spectrally negative Lévy processes on unrelated probability spaces with identical positive Laplace exponents. For any family of measurable integer-valued path functionals count(k,n), assume the canonical model Y has exactly the Poisson zero-count law exp(-δ_k ν_X((−∞,−1/(n+1)])). Then the actual process X has the identical law for the SAME intrinsic path counts. This theorem composes proven Lévy exponent-to-path-law uniqueness with the measurable event {path | count(k,n)(path)=0}. The genuine missing mathematical obligation is constructing the path-functional count and showing it coincides with the canonical Poisson random-measure count; neither is assumed without being explicitly stated.
-- source:
--   Proved cross_levy_path_event_law_of_equal_psi [f2d00bb5-134b-447b-940c-a6b37bca0cc4]. Proved ae_early_downward_jumps_of_levy_band_zero_count_laws [85823b83-fe61-472d-a575-014df1938870] then consumes this result if the count detects actual jumps. Inspiration LeanLevy/RandomMeasure/PoissonRandomMeasure.lean and LevyJumpPath.lean.

import Mathlib.MeasureTheory.Measure.Map
import Theorems.Thm_AvramDividend_Classical_cross_levy_path_event_law_of_equal_psi

open AvramDividend.Classical MeasureTheory Set
open scoped NNReal ENNReal

theorem AvramDividend.Classical.canonical_poisson_band_zero_law_transfer
    {Ω₁ Ω₂ : Type*} [m₁ : MeasurableSpace Ω₁] [m₂ : MeasurableSpace Ω₂]
    {P₁ : Measure Ω₁} {P₂ : Measure Ω₂}
    {𝓕₁ : Filtration ℝ≥0 m₁} {𝓕₂ : Filtration ℝ≥0 m₂}
    (X : SpectrallyNegativeLevy P₁ 𝓕₁)
    (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
    (hψ : ∀ θ : ℝ, 0 < θ → X.ψ θ = Y.ψ θ)
    (δ : ℕ → ℝ≥0)
    (count : ℕ → ℕ → (ℝ≥0 → ℝ) → ℕ)
    (hcount : ∀ k n, Measurable (count k n))
    (hcanonical : ∀ k n,
      P₂ {ω | count k n (fun t : ℝ≥0 => Y.X t ω) = 0} =
      ENNReal.ofReal (Real.exp
        (-((δ k : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal)))) :
    ∀ k n,
      P₁ {ω | count k n (fun t : ℝ≥0 => X.X t ω) = 0} =
      ENNReal.ofReal (Real.exp
        (-((δ k : ℝ) *
          (X.ν (Iic (-(1 / ((n : ℝ) + 1))))).toReal))) := by sorry
