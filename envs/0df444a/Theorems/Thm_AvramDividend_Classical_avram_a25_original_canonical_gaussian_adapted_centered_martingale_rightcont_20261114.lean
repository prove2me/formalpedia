-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a25_original_canonical_gaussian_adapted_centered_martingale_rightcont_20261114
-- name    : AvramDividend.Classical.avram_a25_original_canonical_gaussian_adapted_centered_martingale_rightcont_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T00:16:15.396073+00:00
-- url     : https://prove2.me/theorems/4ab4398c-5289-4899-8301-c5ca207a94f3
-- title:
--   Original Gaussian canonical raw-filtration adapted centred martingale with conull right-continuous paths
-- statement:
--   An original finite-activity spectrally negative Levy source has an everywhere zero-start, raw-filtration adapted Gaussian intrinsic residual representative, integrable centred and a right-continuous-past martingale, with right-continuous paths on a common conull event.
-- source:
--   Proved e33982e1, 86d89070, 45dec03a, 5bdde16f.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
import Theorems.Thm_AvramDividend_Classical_avram_a24_canonical_gaussian_martingale_20261114
import Theorems.Thm_AvramDividend_Classical_avram_a24_physical_gaussian_limit_rightcont_on_source_conull_20261113
import Theorems.Thm_AvramDividend_Classical_avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113
open MeasureTheory ProbabilityTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

/-- The original Gaussian canonical adapted centred martingale has conull right-continuous paths. -/

theorem AvramDividend.Classical.avram_a25_original_canonical_gaussian_adapted_centered_martingale_rightcont_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤) :
    ∃ G : ℝ≥0 → Ω → ℝ,
      (∀ t, Measurable[𝓕 t] (G t)) ∧
      (∀ ω, G 0 ω = 0) ∧
      (∀ᵐ ω ∂P, ∀ t : ℝ≥0,
        ContinuousWithinAt (fun u : ℝ≥0 => G u ω) (Ici t) t) ∧
      (∀ t : ℝ≥0, Integrable (G t) P ∧
        (∫ ω, G t ω ∂P) = 0) ∧
      (∀ s t : ℝ≥0, s ≤ t →
        ∀ᵐ ω ∂P,
          condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by sorry
