-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ja18_original_cutoff_gaussian_square_expectation
-- name    : AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_expectation
-- status  : Open
-- author  : @WillR
-- created : 2026-11-10T20:52:11.40157+00:00
-- url     : https://prove2.me/theorems/cd5dbc12-58fc-47e1-8745-b55b07bd2c9e
-- title:
--   Exact original finite-cutoff Gaussian variance once square integrability is given
-- statement:
--   Once all original finite-cutoff squared Gaussian residuals are integrable, establish their exact expected square equals time times Gaussian variance plus the strict near-zero quadratic Levy correction. Separate the source covariance and compensation calculations from integrability.
-- source:
--   Exact second conjunct of 74450e6a conditional on the first conjunct. The truncation lower endpoint is strict because the compensated mark band includes the cutoff boundary. Work on original same-Ω filtration; comparison models require a proved law identification.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_ja18_original_cutoff_gaussian_square_expectation
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hSq : (∀ (n : ℕ) (t : ℝ≥0), Integrable
      (fun ω => (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2) P)) :
    ∀ (n : ℕ) (t : ℝ≥0),
      (∫ ω, (avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω) ^ 2 ∂P) =
        (t : ℝ) * X.σ ^ 2 +
          (t : ℝ) * (∫ z in Ioo (-(1 / ((n : ℝ) + 1))) 0, z ^ 2 ∂X.ν) := by sorry
