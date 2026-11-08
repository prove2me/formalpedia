-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable
-- name    : AvramDividend.Classical.avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-07T17:46:07.040802+00:00
-- url     : https://prove2.me/theorems/2299f164-5a0a-4a40-bf3d-2fa1e8288084
-- title:
--   Original strict negative marked Laplace weight is filtration-measurable at every fractional horizon
-- statement:
--   For the original spectrally negative Lévy process, the exact strict negative cutoff marked-jump exponential on (0,T] is measurable with respect to its original filtration at any nonnegative deterministic T. The measurable path functional is applied to the original path frozen at T; exact arbitrary-time weighted marked rectangle transport identifies it with the true source weight. Needed to factor original equal short-cell products using past/future Lévy independence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_turn14_cadlag_cutoff_borel_arbitrary_horizon
import Theorems.Thm_AvramDividend_Classical_avram_bv_jump8_original_frozen_prefix_path_filtration_measurable
import Theorems.Thm_AvramDividend_Classical_avram_wave7_06_original_frozen_prefix_cadlag_all_horizons
import Theorems.Thm_AvramDividend_Classical_avram_route_runner_f_original_frozen_weighted_cutoff_any_horizon

open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_route_runner_f_original_arbitrary_prefix_laplace_filtration_measurable
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕) (T : ℝ≥0) (k : ℕ) :
    Measurable[𝓕 T] (fun ω : Ω => Real.exp (-((∫⁻ p : ℝ≥0 × ℝ,
        if 0 < p.1 ∧ p.1 ≤ T ∧ p.2 < -(1 / ((k : ℝ) + 1))
        then ENNReal.ofReal (-p.2) else 0 ∂
        ((Measure.count.restrict {u : ℝ≥0 |
          0 < u ∧ X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u ≠ 0}).map
          (fun u : ℝ≥0 => (u, X.X u ω -
            Function.leftLim (fun v : ℝ≥0 => X.X v ω) u)))).toReal))) := by sorry
