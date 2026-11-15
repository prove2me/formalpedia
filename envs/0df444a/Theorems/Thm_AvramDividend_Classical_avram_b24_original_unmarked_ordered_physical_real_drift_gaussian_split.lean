-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b24_original_unmarked_ordered_physical_real_drift_gaussian_split
-- name    : AvramDividend.Classical.avram_b24_original_unmarked_ordered_physical_real_drift_gaussian_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T21:31:34.31624+00:00
-- url     : https://prove2.me/theorems/b4e829e8-1b75-4153-896d-d158eb902220
-- title:
--   Original ordered unmarked physical Gaussian cells use real-time compensated drift differences
-- statement:
--   The original finite-activity intrinsic Lévy same-source decomposition and marked-cell split imply that every ordered physical cell without a genuine source jump has centred increment equal to the intrinsic Gaussian increment plus the deterministic smallmark compensator times the ordinary real difference of its endpoints. Retains actual source X and right-continuous filtration martingales.
-- source:
--   Proved b213 original intrinsic same-source martingale and canonical unmarked-cell split; Mathlib NNReal.coe_sub at the exact pinned Mathlib revision.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b24_original_unmarked_ordered_physical_real_drift_gaussian_split
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)

    (S : Finset ℕ) (s t : ℕ → Ω → ℝ≥0)
    (hOrdered : ∀ ω i, i ∈ S → s i ω ≤ t i ω)
    (J : Ω → Finset ℕ)
    (hJcanon : ∀ ω i, i ∈ J ω ↔ i ∈ S ∧
      ∃ u : ℝ≥0, s i ω < u ∧ u ≤ t i ω ∧
        X.X u ω - Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0)
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
        avram_p4_h_gaussian_intrinsic_large_jump_sum X u ω) ∧
      (∀ᵐ ω ∂P, ∀ i, i ∈ S → i ∉ J ω →
        X.X (t i ω) ω - X.X (s i ω) ω -
          ((t i ω : ℝ) - (s i ω : ℝ)) * X.c =
        (R (t i ω) ω - R (s i ω) ω) +
          (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
            ((t i ω : ℝ) - (s i ω : ℝ))):= by sorry
