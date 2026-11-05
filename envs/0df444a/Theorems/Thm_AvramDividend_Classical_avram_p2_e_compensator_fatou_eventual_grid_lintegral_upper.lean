-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p2_e_compensator_fatou_eventual_grid_lintegral_upper
-- name    : AvramDividend.Classical.avram_p2_e_compensator_fatou_eventual_grid_lintegral_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-04T16:38:53.31399+00:00
-- url     : https://prove2.me/theorems/e57ecc39-e627-481a-8c0c-2f7323762cd2
-- title:
--   Fatou transfers eventually exact measurable original grid pair counts to the limiting mean
-- statement:
--   For any measure and measurable nonnegative extended-real grid counts G, if each sample path eventually has G_n equal to its chronological pair count K, Fatou's lemma bounds the integral of K above by the liminf of the grid-count integrals. No inter-grid monotonicity is required.
-- source:
--   Pinned MeasureTheory.lintegral_liminf_le and Filter.liminf_congr / Filter.liminf_const, used for source-exact original negative-band second factorial moment passage after source pathwise eventual equality.

import Mathlib

open MeasureTheory Filter
open scoped ENNReal

theorem AvramDividend.Classical.avram_p2_e_compensator_fatou_eventual_grid_lintegral_upper
    {Ω : Type*} [MeasurableSpace Ω]
    (μ : MeasureTheory.Measure Ω) (G : ℕ → Ω → ℝ≥0∞) (K : Ω → ℝ≥0∞)
    (hMeas : ∀ n, Measurable (G n))
    (hEventual : ∀ ω, ∀ᶠ n in Filter.atTop, G n ω = K ω) :
    (∫⁻ ω, K ω ∂μ) ≤
      Filter.liminf (fun n : ℕ => ∫⁻ ω, G n ω ∂μ) Filter.atTop := by sorry
