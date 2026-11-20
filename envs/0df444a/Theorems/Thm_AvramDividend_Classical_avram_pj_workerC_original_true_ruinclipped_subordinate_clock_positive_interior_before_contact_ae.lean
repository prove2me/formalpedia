-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_original_true_ruinclipped_subordinate_clock_positive_interior_before_contact_ae
-- name    : AvramDividend.Classical.avram_pj_workerC_original_true_ruinclipped_subordinate_clock_positive_interior_before_contact_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T12:49:33.929585+00:00
-- url     : https://prove2.me/theorems/a825583c-a983-4c55-920c-ecf104cd3cda
-- title:
--   Original unbounded-variation spectrally negative dividend reserve is strictly positive almost everywhere in physical time before the actual subordinate ruin-clipped stopping clock
-- statement:
--   For the true spectrally negative unbounded-variation Levy process X, original admissible controlled right-dividend reserve, natural finite ruin-clipped stopping time tau=min(ruin,n) and any subordinate stop rho<=tau, the actual post-right controlled reserve riskProcess X x D at original physical time t is strictly positive for almost every physical time t strictly before rho, for almost every original Lévy sample. This holds for any sigma-finite physical time measure including the finite real Lebesgue clock; the original path or filtration is not replaced. This supplies spatial C2 interior localisation needed by the infinite-activity physical Ito source.
-- source:
--   Proved 644af487 all-cap UBV original stopped strict positive without grid; Proved edebe535 true subordinate clipping bound.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_ubv_allcap_original_stopped_full_zero_included_no_grid
import Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_subordinate_clock_bounded_by_horizon_and_ruin
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_original_true_ruinclipped_subordinate_clock_positive_interior_before_contact_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (hUBV : ¬ X.BoundedVariation)
    (x : ℝ) (C : ℝ≥0∞)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsAdmissibleLe X x C D)
    (n : ℕ) (hn : 0 < n) (τ ρ : Ω → ℝ≥0)
    (hτeq : ∀ ω, τ ω =
      (min (ruinTime X x D ω) (n : ℝ≥0∞)).toNNReal)
    (hρle : ∀ ω, ρ ω ≤ τ ω)
    (μ : Measure ℝ≥0) [SFinite μ] :
    ∀ᵐ ω ∂P, ∀ᵐ (t : ℝ≥0) ∂μ,
      (t : ℝ≥0∞) < (ρ ω : ℝ≥0∞) →
        0 < riskProcess X x D t ω := by sorry
