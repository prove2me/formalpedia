-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
-- name    : AvramDividend.Classical.avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T13:20:58.285037+00:00
-- url     : https://prove2.me/theorems/b4677f24-9236-4a4a-a328-60090436e1e8
-- title:
--   Original finite ruin-truncated clock strict/inclusive endpoint equivalence and T=0
-- statement:
--   For the literal original SpectrallyNegativeLevy ruinTime and deterministic NNReal horizon T, the real-valued ruin-truncated clock tau has exact strict and inclusive comparisons. t<tau iff t<ruinTime and t<T; t<=tau iff t<=ruinTime and t<=T. If T=0, tau=0. This resolves stopped-grid endpoint conventions for P3-F and avoids treating inclusive compensation masks as strict pre-ruin payoff masks.
-- source:
--   Mathlib ENNReal.coe_toNNReal for finite min(ruinTime,T), min order laws, and actual original ruinTime; no assumption of boundary occupation or change of process.

import Mathlib.MeasureTheory.MeasurableSpace.Defs
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy

open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_p3_g_localise_original_ruin_clock_exact_strict_inclusive_endpoints
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (x : ℝ)
    (D : ℝ≥0 → Ω → ℝ) (T : ℝ≥0) :
    let τ : Ω → ℝ≥0 := fun ω =>
      (min (ruinTime X x D ω) (T : ℝ≥0∞)).toNNReal
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) < (τ ω : ℝ≥0∞) ↔
        (t : ℝ≥0∞) < ruinTime X x D ω ∧ t < T) ∧
    (∀ ω (t : ℝ≥0),
      (t : ℝ≥0∞) ≤ (τ ω : ℝ≥0∞) ↔
        (t : ℝ≥0∞) ≤ ruinTime X x D ω ∧ t ≤ T) ∧
    (T = 0 → ∀ ω, τ ω = 0) := by sorry
