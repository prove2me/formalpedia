-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_finite_activity_companion_square_decomposition
-- name    : AvramDividend.Classical.avram_ja19_finite_activity_companion_square_decomposition
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T12:00:28.210909+00:00
-- url     : https://prove2.me/theorems/51a94017-55a4-41e5-a586-babae5bd64fd
-- title:
--   Countable same-triplet finite-activity companion with Gaussian and bounded-jump L2 components
-- statement:
--   Build on the real sequence standard Borel probability space a spectrally negative Levy process with precisely the original characteristic triplet. In its explicit Brownian-plus-finite-activity compound-Poisson construction, isolate a square-integrable Gaussian component and a square-integrable bounded-jump compensator whose sum is the canonical intrinsic zero-cutoff residual almost surely. The large negative jumps are cancelled by the residual definition and do not require any second or first moment.
-- source:
--   J-A19 finite activity Gaussian bracket canonical construction; finite-activity compound-Poisson and Brownian existence

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja19_finite_activity_companion_square_decomposition
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (t : ℝ≥0) :
    ∃ (P₂ : Measure (ℕ → ℝ))
      (𝓕₂ : Filtration ℝ≥0 (inferInstance : MeasurableSpace (ℕ → ℝ)))
      (Y : SpectrallyNegativeLevy P₂ 𝓕₂)
      (G J : (ℕ → ℝ) → ℝ),
      X.c = Y.c ∧ X.σ = Y.σ ∧ X.ν = Y.ν ∧
      Integrable (fun ω : ℕ → ℝ => (G ω) ^ 2) P₂ ∧
      Integrable (fun ω : ℕ → ℝ => (J ω) ^ 2) P₂ ∧
      (∀ᵐ ω ∂P₂,
        avram_p4_h_gaussian_intrinsic_truncated_residual Y 0 t ω =
          G ω + J ω) := by sorry
