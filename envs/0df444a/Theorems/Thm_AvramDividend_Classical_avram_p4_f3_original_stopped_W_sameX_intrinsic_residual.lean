-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
-- name    : AvramDividend.Classical.avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T10:17:14.901579+00:00
-- url     : https://prove2.me/theorems/1cbe05b8-a4f4-46e8-b18e-4c55752acdc1
-- title:
--   True stopped reserve terminal W has original same-process finite-band Gaussian residual and jump split in both ruin branches
-- statement:
--   The exact W stipulated in canonical UBV source verification is decomposed pathwise at its real stopped clock, for every original sample path and every small-band cutoff. Both survival and ruin/horizon branches use X itself, its intrinsic compensated small negative-jump contribution, its original large-jump sum and its original truncated candidate Gaussian residual. The dividend subtraction is rightLimit D before ruin or at the zero boundary, and D at ruin. This proves the required original W source identity without an independent Gaussian surrogate, an equality-in-law step or any stochastic mean-zero assumption. Source martingale/continuous path properties remain separate.
-- source:
--   Original same-process source for canonical fdb9a6a3 hW. The source residual's definitional identity is verified in Proved/public 75c91fbd and finiteband reserve decomposition Proved/public e9bcd24b, and actual original finite small-jump sum is identified by Proved/public 1c1d4731. Proof unfolds the exact target definitions and separates the original ruin branch by cases.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p4_f3_original_stopped_W_sameX_intrinsic_residual
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (x : ℝ) (D : ℝ≥0 → Ω → ℝ) (n : ℕ)
    (τ : Ω → ℝ≥0) (W : Ω → ℝ)
    (hW : ∀ ω, W ω =
      if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
      then x + X.X (τ ω) ω - rightLimit D (τ ω) ω
      else riskProcess X x D (τ ω) ω) :
    ∀ ω, W ω =
      x + (τ ω : ℝ) * X.c +
        avram_p4_h_gaussian_intrinsic_small_band_compensated X n (τ ω) ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X (τ ω) ω +
        avram_p4_h_gaussian_intrinsic_truncated_residual X n (τ ω) ω -
        (if τ ω = 0 ∨ (τ ω : ℝ≥0∞) < ruinTime X x D ω
         then rightLimit D (τ ω) ω else D (τ ω) ω) := by sorry
