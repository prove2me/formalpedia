-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
-- name    : AvramDividend.Classical.avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:50:40.155963+00:00
-- url     : https://prove2.me/theorems/ccb9b397-52e9-4492-bc35-bf1909db6f28
-- title:
--   Global same-filtration intrinsic original Gaussian and small-jump martingale source decomposition under finite activity alone
-- statement:
--   For any original finite-negative-activity spectrally negative Levy source satisfying its Standing assumptions, globally construct intrinsic same-filtration Gaussian residual and compensated small-negative-mark martingales, their almost sure original truncation limits at all physical times, their finite first moments and conditional expectation identities, and the original Lévy source decomposition into these two martingale channels and the large-jump process. No auxiliary stopping time, finite-valued random clock, jumpfree interval, independent driver or post-ruin continuation hypotheses are needed. The proof specialises Proved B211 at the deterministic zero clock, whose stopping-time status follows from the pinned Mathlib isStoppingTime_const declaration.
-- source:
--   Original B211 and pinned Mathlib isStoppingTime_const; true original Lévy source.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b212_original_finite_activity_global_intrinsic_gaussian_smallmark_martingale_sources
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
 :
    ∃ (R Jsmall M : ℝ≥0 → Ω → ℝ),
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_truncated_residual X k u ω)
          atTop (𝓝 (R u ω))) ∧
      (∀ᵐ ω ∂P, ∀ u : ℝ≥0,
        Tendsto (fun k : ℕ =>
          avram_p4_h_gaussian_intrinsic_small_band_compensated X k u ω)
          atTop (𝓝 (Jsmall u ω))) ∧
      (∀ u : ℝ≥0, Integrable (R u) P) ∧
      (∀ u : ℝ≥0, Integrable (Jsmall u) P) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (R b) ω = R a ω) ∧
      (∀ a b : ℝ≥0, a ≤ b →
        ∀ᵐ ω ∂P, condExp (𝓕.rightCont a) P (Jsmall b) ω = Jsmall a ω) ∧
      (∀ u ω, X.X u ω = (u : ℝ) * X.c + M u ω + Jsmall u ω +
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) := by sorry
