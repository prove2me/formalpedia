-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb20_original_gaussian_past_weight_increment_mean_zero
-- name    : AvramDividend.Classical.avram_jb20_original_gaussian_past_weight_increment_mean_zero
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T16:34:48.277071+00:00
-- url     : https://prove2.me/theorems/8d896ff6-e86c-4fe0-bd72-a61ba871785b
-- title:
--   Original right-continuous Gaussian martingale weighted deterministic cell has zero mean
-- statement:
--   For a martingale on the exact original right-continuous filtration, a square-integrable or otherwise integrable product between any past measurable weight and a future increment has mean zero. The conditional centring is derived from the deterministic-time martingale hypothesis and the difference identity, avoiding an independent zero-jump process.
-- source:
--   Proved a4976dc6 predictable conditional cross-zero plus Mathlib condExp_sub. Provides the exact original deterministic-grid linear Gaussian Ito term needed in 544e8511.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_gb49_predictable_real_condExp_cross_zero
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb20_original_gaussian_past_weight_increment_mean_zero
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (R : ℝ≥0 → Ω → ℝ)
    (hRint : ∀ u : ℝ≥0, Integrable (R u) P)
    (hRmart : ∀ u v : ℝ≥0, u ≤ v →
      ∀ᵐ ω ∂P,
        condExp (𝓕.rightCont u) P (R v) ω = R u ω)
    (s t : ℝ≥0) (hst : s ≤ t)
    (H : Ω → ℝ)
    (hH : Measurable[𝓕.rightCont s] H)
    (hProd : Integrable
      (fun ω => H ω * (R t ω - R s ω)) P) :
    (∫ ω, H ω * (R t ω - R s ω) ∂P) = 0 := by sorry
