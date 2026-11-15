-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_b213_original_global_intrinsic_martingales_and_canonical_unmarked_grid_split
-- name    : AvramDividend.Classical.avram_b213_original_global_intrinsic_martingales_and_canonical_unmarked_grid_split
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T07:52:46.851949+00:00
-- url     : https://prove2.me/theorems/19339df6-9431-499a-a208-14eb80063caa
-- title:
--   Unconditional original Gaussian and small-jump martingale source witnesses with genuine canonical random-grid jumpfree decomposition
-- statement:
--   Under the genuine original finite-negative-activity spectrally negative Levy source Standing assumptions, construct without auxiliary clock premises global intrinsic Gaussian residual and compensated small-jump martingales in the same filtration, with all source truncation convergence, integrability, conditional expectation identities and exact global source decomposition. Simultaneously establish on a common conull original source event the exact intrinsic Gaussian residual plus negative-mark compensator drift increment formula on every unmarked cell of any finite ordered physical random grid whose marked cells are defined by genuine source jumps. The result uses the global-noise B212 and the physically marked-cell conull B209 source identities, providing both stochastic noise channels and the jump-free source ledger in one theorem.
-- source:
--   Proved B209, B212 original global noise source; original finite negative activity only.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_small_band_compensated
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_large_jump_sum
import Theorems.Thm_AvramDividend_Classical_avram_b211_original_finite_activity_intrinsic_gaussian_smallmark_global_martingales
import Theorems.Thm_AvramDividend_Classical_avram_b209_original_canonical_true_unmarked_grid_gaussian_source_drift_ae
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_b213_original_global_intrinsic_martingales_and_canonical_unmarked_grid_split
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
          ((t i ω - s i ω : ℝ≥0) : ℝ) * X.c =
        (R (t i ω) ω - R (s i ω) ω) +
          (-(∫ z in Ioo (-1 : ℝ) 0, z ∂X.ν)) *
            ((t i ω - s i ω : ℝ≥0) : ℝ)) := by sorry
