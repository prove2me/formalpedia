-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
-- name    : AvramDividend.Classical.avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-01T10:08:30.909302+00:00
-- url     : https://prove2.me/theorems/644af487-db5d-4d41-995b-5576891a3013
-- title:
--   Schedule-free original UBV stopped zero occupation including an atom at time zero
-- statement:
--   For the exact original-filtration unbounded-variation Lévy process X and the actual capped admissible dividend strategy D, at any ruin-dominated original sample-path localising clock σ and under arbitrary sigma-finite observation-time measure μ, the controlled reserve is strictly positive μ-almost everywhere before σ on P-almost every path, even when μ has an atom at time zero. No dense observation grid or cofinal horizon family is required; all original caps including zero and infinity are permitted. Positive times use the independently remotely accepted allcap grid-free stopped positivity theorem. The potentially exceptional time zero is handled separately via the Proved unbounded-variation downward regularity at original-filtration finite stopping times, specialised to the deterministic zero stopping time, with the genuine pre-ruin nonnegative reserve theorem. This establishes the full zero-occupation interface independent of point-mass restrictions on μ. It says nothing about dividend Stieltjes jump mass, which remains under other researchers.
-- source:
--   Corrected UBV core 429e17ca-5528-40b5-b593-7c03973d0706. Proved no-grid positive times 35d7d09c-385f-4fc7-bed3-d863cc271c59. Proved original finite stopping-time strict positivity aa42a21a-9b17-47b3-b72d-a6efd383ae5c. Proved actual reserve nonnegativity before ruin. No source filtration change, no added boundary assumptions, no milestone/core updates.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_riskProcess_nonneg_before_ruin
import Theorems.Thm_AvramDividend_Classical_avram_wave4_04_ubv_original_controlled_preruin_finite_stopping_strict_positive
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_positive_no_grid

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal

theorem AvramDividend.Classical.avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (σ : Ω → ℝ≥0∞)
    (hσ : ∀ ω, σ ω ≤ ruinTime X x D ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < σ ω →
        0 < riskProcess X x D t ω := by sorry
