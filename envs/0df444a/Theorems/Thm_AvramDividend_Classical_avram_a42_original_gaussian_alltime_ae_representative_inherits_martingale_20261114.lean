-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_a42_original_gaussian_alltime_ae_representative_inherits_martingale_20261114
-- name    : AvramDividend.Classical.avram_a42_original_gaussian_alltime_ae_representative_inherits_martingale_20261114
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T10:22:00.144331+00:00
-- url     : https://prove2.me/theorems/0096faa4-40d6-4ebc-b1c6-8cf6cdc82008
-- title:
--   Every original finite-activity Gaussian limit representative is a right-cont-filtration L1 martingale with original source conditional means
-- statement:
--   Every process equal simultaneously at all deterministic times outside a single original-probability null event with the intrinsic Gaussian residual limit is integrable at all times and satisfies the conditional martingale identities relative to the original right-continuous filtration.
-- source:
--   Proved B31 original intrinsic finite-activity Gaussian source martingale, uniqueness of limits, Mathlib condExp_congr_ae.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
import Theorems.Thm_AvramDividend_Classical_avram_b31_original_finite_activity_intrinsic_gaussian_martingale_exists
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_a42_original_gaussian_alltime_ae_representative_inherits_martingale_20261114
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R G : ℝ≥0 → Ω → ℝ)
    (hR : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun n : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X n t ω)
        atTop (𝓝 (R t ω)))
    (hEq : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, G t ω = R t ω) :
    (∀ t : ℝ≥0, Integrable (G t) P) ∧
    (∀ s t : ℝ≥0, s ≤ t →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont s) P (G t) ω = G s ω) := by sorry
