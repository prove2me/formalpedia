-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a29_original_positive_sigma_intrinsic_gaussian_raw_allpath_cadlag
-- name    : AvramDividend.Classical.avram_a29_original_positive_sigma_intrinsic_gaussian_raw_allpath_cadlag
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T08:06:05.867204+00:00
-- url     : https://prove2.me/theorems/ea9b7dc3-e9aa-4012-ae28-d1754580bbb2
-- title:
--   Positive-volatility original Gaussian physical cutoff limit admits globally raw-adapted all-path cadlag no-positive-jump modification
-- statement:
--   Construct the fully pathwise cadlag, no-positive-jump version of the positive-volatility Gaussian intrinsic residual on exactly the original filtered probability space with no filtration completion or external noise, agreeing with the compact-uniform physical limit on a common conull event.
-- source:
--   Original finite-activity physical jump-source regularisation via nonanticipative pathwise jump removal, avoiding completion assumptions.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a29_original_positive_sigma_intrinsic_gaussian_raw_allpath_cadlag
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (hPositive : 0 < X.σ)
    (R : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω))) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t, G t ω = R t ω) ∧
      (∀ ω t, ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ ω t, 0 < t →
        ∃ l, Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l)) ∧
      (∀ ω t l, 0 < t →
        Tendsto (fun u : ℝ≥0 => G u ω) (𝓝[<] t) (𝓝 l) →
        G t ω ≤ l) := by sorry
