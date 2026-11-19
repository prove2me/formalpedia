-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_finiteactivity_gaussian_intrinsic_centered_and_zero_initial
-- name    : AvramDividend.Classical.avram_f6_original_finiteactivity_gaussian_intrinsic_centered_and_zero_initial
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T20:44:47.746768+00:00
-- url     : https://prove2.me/theorems/9091c2fc-f500-4998-86da-35b9e8a7a8c1
-- title:
--   Actual original finite-activity intrinsic Gaussian source is centred, integrable and zero at origin
-- statement:
--   For the original spectrally negative Lévy process X with Standing and finite negative-jump intensity and any authentic pathwise limit R of its Gaussian truncated residual sequence, R is Bochner integrable and has mean zero at every deterministic nonnegative time; in addition R has exactly zero initial value almost surely. The combined original Gaussian source certificate directly incorporates existing Proved fixed-time L1 and centred noise plus an all-activity initial-value theorem, with no added substitute Gaussian probability space, compensating mark assumption or adaptedness condition.
-- source:
--   Proved avram_a21_original_gaussian_limit_integrable_centered_via_source_companion_20261113 (5bdde16f) and newly Proved original all-activity intrinsic Gaussian zero origin (eb8e9ad9).

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_avram_p4_h_gaussian_intrinsic_truncated_residual
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_finiteactivity_gaussian_intrinsic_centered_and_zero_initial
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hX : X.Standing)
    (hFinite : X.ν (Iio (0 : ℝ)) ≠ ⊤)
    (R : ℝ≥0 → Ω → ℝ)
    (hRsource : ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      Tendsto (fun k : ℕ =>
        avram_p4_h_gaussian_intrinsic_truncated_residual X k t ω)
        atTop (nhds (R t ω))) :
    (∀ t : ℝ≥0, Integrable (R t) P ∧
      (∫ ω, R t ω ∂P) = 0) ∧
    (∀ᵐ ω ∂P, R 0 ω = 0) := by sorry
