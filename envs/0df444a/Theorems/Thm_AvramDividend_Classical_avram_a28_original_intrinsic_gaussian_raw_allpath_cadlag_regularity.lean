-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a28_original_intrinsic_gaussian_raw_allpath_cadlag_regularity
-- name    : AvramDividend.Classical.avram_a28_original_intrinsic_gaussian_raw_allpath_cadlag_regularity
-- status  : Open
-- author  : @WillR
-- created : 2026-11-14T07:54:13.626312+00:00
-- url     : https://prove2.me/theorems/e6d3968a-1ee3-46dd-8eea-d1ea09d91f27
-- title:
--   Original Gaussian intrinsic residual admits all-path raw-adapted zero-start cadlag spectrally negative regularisation
-- statement:
--   Construct a globally original-F_t adapted, all-path right-continuous, left-limited, no-positive-jump modification equal simultaneously at all times almost surely to the intrinsic Gaussian limit R of a finite-activity spectrally negative original Levy source.
-- source:
--   Original A24/A27 source constructions; remaining genuine finite-activity path or Lévy-Khintchine analytic proof.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a28_original_intrinsic_gaussian_raw_allpath_cadlag_regularity
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
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
