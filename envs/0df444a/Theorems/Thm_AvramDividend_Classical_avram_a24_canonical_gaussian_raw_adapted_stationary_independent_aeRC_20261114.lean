-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a24_canonical_gaussian_raw_adapted_stationary_independent_aeRC_20261114
-- name    : AvramDividend.Classical.avram_a24_canonical_gaussian_raw_adapted_stationary_independent_aeRC_20261114
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T00:15:26.683368+00:00
-- url     : https://prove2.me/theorems/1e9ae8de-1cda-4d1e-afac-5953dc309b34
-- title:
--   One original Gaussian residual process is raw-filtration adapted with stationary independent increments and a.e. all-time right continuity
-- statement:
--   There is one globally original-filtration adapted, exact-zero Gaussian intrinsic residual process with genuinely independent and stationary increments and right-continuous paths on a single source full-measure event, agreeing almost surely with the physical residual.
-- source:
--   Proved A24 globally adapted AE right-continuous Gaussian source, A24 original independent increments, AE independence invariance and original Gaussian stationary increments.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_a24_original_gaussian_limit_increment_stationary_law_20261113
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The physical source Gaussian limit has one adapted almost surely right-continuous process with stationary independent increments. -/

theorem AvramDividend.Classical.avram_a24_canonical_gaussian_raw_adapted_stationary_independent_aeRC_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hRate : ∀ᵐ ω ∂P, ∀ K : ℕ, ∀ ε : ℝ, 0 < ε →
      ∃ N : ℕ, ∀ n ≥ N, ∀ T : ℝ≥0, T ≤ (K : ℝ≥0) →
        |avram_p4_h_gaussian_intrinsic_truncated_residual X n T ω -
          R T ω| ≤ ε) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω : Ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ᵐ ω ∂P, ∀ t,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ s T : ℝ≥0, Indep
        (MeasurableSpace.comap (fun ω => G (s + T) ω - G s ω) inferInstance)
        (𝓕 s) P) ∧
      (∀ T, ∃ Z : Ω → ℝ, Measurable Z ∧
        ∀ s : ℝ≥0,
          Measure.map (fun ω => G (s + T) ω - G s ω) P =
          Measure.map Z P) := by sorry
