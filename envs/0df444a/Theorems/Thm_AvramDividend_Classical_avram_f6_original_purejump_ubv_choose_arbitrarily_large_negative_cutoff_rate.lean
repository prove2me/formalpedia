-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_f6_original_purejump_ubv_choose_arbitrarily_large_negative_cutoff_rate
-- name    : AvramDividend.Classical.avram_f6_original_purejump_ubv_choose_arbitrarily_large_negative_cutoff_rate
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T17:10:39.030314+00:00
-- url     : https://prove2.me/theorems/c8476ba7-764c-4789-aaa8-bae409809985
-- title:
--   Choose a finite negative-jump truncation with arbitrarily large intensity for original purejump UBV
-- statement:
--   For any real intensity target R, an original spectrally negative purejump unbounded-variation Lévy driver admits a positive negative-mark cutoff δ with actual truncated rate ν((-∞,-δ)) at least R. This supplies an explicit finite-intensity but arbitrarily high-rate approximation scale for the infinite-activity compensated jump physical source. The theorem is a direct consequence of the Proved original truncated-rate divergence and avoids assuming the full stopped dividend verification budget.
-- source:
--   Proved original truncated negative rate divergence 5da6ed6a pending 42095, Proved generic negative_jump_real_tail_tendsto_top 2cde304a.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_f6_original_purejump_ubv_choose_arbitrarily_large_negative_cutoff_rate
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (hBV : ¬ X.BoundedVariation) (hσ : X.σ = 0)
    (R : ℝ) :
    ∃ δ : ℝ, 0 < δ ∧ R ≤ (X.ν (Iio (-δ))).toReal := by sorry
