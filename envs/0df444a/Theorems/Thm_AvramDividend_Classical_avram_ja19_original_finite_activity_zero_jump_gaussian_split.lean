-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja19_original_finite_activity_zero_jump_gaussian_split
-- name    : AvramDividend.Classical.avram_ja19_original_finite_activity_zero_jump_gaussian_split
-- status  : Open
-- author  : @WillR
-- created : 2026-11-11T12:29:30.826243+00:00
-- url     : https://prove2.me/theorems/9d10a5f9-a0c6-4cd9-8ea0-4244cd7402de
-- title:
--   Original same-space Lévy process admits a zero-jump Gaussian component and L2 bounded jump remainder
-- statement:
--   Under finite negative-jump activity construct on the original probability space P and original right-continuous filtration 𝓕 a spectrally negative Lévy process Y with zero Lévy measure and the same Gaussian coefficient. Remove actual pathwise finite jumps and account for the compensated small-jump drift. At fixed t the original intrinsic residual at cutoff zero equals the centred Y increment plus a square-integrable bounded-jump compensator, almost surely. This is the original-space Lévy-Itô decomposition needed to invoke an already Proved zero-ν quadratic lemma.
-- source:
--   J-A19 alternative to countable comparison model, zero-nu quadratic conditional expectation 58eec8bb Proved, negative finite count L2 a6562a4d Proved

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_ja19_original_finite_activity_zero_jump_gaussian_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) (t : ℝ≥0) :
    ∃ (Y : SpectrallyNegativeLevy P 𝓕) (J : Ω → ℝ),
      Y.ν = 0 ∧ Y.σ = X.σ ∧
      Integrable (fun ω => (J ω) ^ 2) P ∧
      (∀ᵐ ω ∂P,
        avram_p4_h_gaussian_intrinsic_truncated_residual X 0 t ω =
          (Y.X t ω - (t : ℝ) * Y.c) + J ω) := by sorry
