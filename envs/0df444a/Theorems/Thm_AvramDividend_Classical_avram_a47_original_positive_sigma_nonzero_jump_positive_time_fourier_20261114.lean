-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
-- name    : AvramDividend.Classical.avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T10:35:32.399618+00:00
-- url     : https://prove2.me/theorems/1c2c3e4c-95da-41a0-805d-a96ceb4eb3ff
-- title:
--   Exact original positive-time intrinsic Gaussian Fourier marginal for finite but nonzero negative-jump intensity and positive sigma
-- statement:
--   For finite nonzero negative-jump intensity and positive Gaussian volatility, calculate the original physical intrinsic Gaussian cutoff limit characteristic function at strictly positive times directly from the actual original spectrally negative Lévy source and its physical jump marks. This is the remaining nontrivial branch after the zero-time, zero-jump and zero-volatility laws have been proved.
-- source:
--   Source-faithful finite negative-jump cancellation in Lévy–Khintchine, positive-sigma nonzero-nu regime; Avram–Palmowski–Pistorius (2007) §2.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_a47_original_positive_sigma_nonzero_jump_positive_time_fourier_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ) (hNu : X.ν ≠ 0)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (G : ℝ≥0 → Ω → ℝ)
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    ∀ (t : ℝ≥0) (ht : 0 < t) (u : ℝ),
      charFun (P.map (G t)) u =
        charFun (gaussianReal 0
          (NNReal.mk ((t : ℝ) * X.σ ^ 2)
            (mul_nonneg (NNReal.coe_nonneg t) (sq_nonneg X.σ)))) u := by sorry
