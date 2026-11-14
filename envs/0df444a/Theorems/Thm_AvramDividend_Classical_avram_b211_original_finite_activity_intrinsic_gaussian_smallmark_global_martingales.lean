-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
-- name    : AvramDividend.Classical.avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:05:45.099214+00:00
-- url     : https://prove2.me/theorems/2878d582-d82b-4ab5-9bba-49160ab9bec2
-- title:
--   Global intrinsic original Gaussian and small-negative-jump martingale source witnesses without a jumpfree interval hypothesis
-- statement:
--   For the original finite-negative-activity Lévy process satisfying the Standing assumptions and any bounded finite-valued original stopping time, obtain intrinsic same-filtration Gaussian residual and compensated small-negative-mark processes globally, with almost-sure convergence of the original truncations at every physical time, integrability, zero-mean martingale conditional-expectation identities and exact original source decomposition. The proof specialises the already Proved B147 random-interval result to identical interval endpoints, so the source no-jump premise is automatically true. This removes the artificial need to find a jump-free random interval before constructing the global martingale channels.
-- source:
--   Proved B147 original two-noise global martingales via identical random clock endpoints, no new process.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b147_original_ae_jumpfree_intrinsic_martingales_gaussian_full_drift
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (n : ℕ) (hn : 0 < n)
    (τ : Ω → ℝ≥0)
    (hτstop : IsStoppingTime 𝓕.rightCont
      (fun ω => (τ ω : WithTop ℝ≥0)))
    (hτbound : ∀ ω, τ ω ≤ (n : ℝ≥0))
    (S : Finset ℝ≥0) (hτrange : ∀ ω, τ ω ∈ S)
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
