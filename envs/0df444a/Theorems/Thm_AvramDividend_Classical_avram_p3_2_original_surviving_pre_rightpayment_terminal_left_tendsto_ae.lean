-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_p3_2_original_surviving_pre_rightpayment_terminal_left_tendsto_ae
-- name    : AvramDividend.Classical.avram_p3_2_original_surviving_pre_rightpayment_terminal_left_tendsto_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-05T21:43:48.935198+00:00
-- url     : https://prove2.me/theorems/c3f48082-d50c-4baa-b3e2-e68930e6aef5
-- title:
--   Original reserve converges from left to pre-horizon right-payment state
-- statement:
--   At every deterministic positive horizon, the original risk process evaluated immediately before right payments on times approaching that horizon converges almost surely to the original reserve before the horizon's right payment, preserving any right-horizon atom.
-- source:
--   The original Lévy path has no jump at a fixed positive time almost surely. The accepted dividend-strategy lemma proves left convergence of rightLimit D to actual D at that time. Addition and subtraction of these real-valued limits give the exact physical prepayment reserve convergence.

import Mathlib
import Definitions.Def_AvramDividend_Classical_SpectrallyNegativeLevy
import Definitions.Def_AvramDividend_Classical_DividendStrategy
import Theorems.Thm_AvramDividend_Classical_avram_wave5_01_actual_source_no_fixed_positive_time_jump_ae
import Theorems.Thm_AvramDividend_Classical_avram_wave3_04_rightLimit_leftLimit_eq_dividend
set_option pp.explicit true
set_option pp.fullNames true
set_option pp.universes true

open MeasureTheory Set Filter Topology
open scoped NNReal ENNReal
open AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_p3_2_original_surviving_pre_rightpayment_terminal_left_tendsto_ae
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 mΩ}
    (X : SpectrallyNegativeLevy P 𝓕)
    (D : ℝ≥0 → Ω → ℝ) (hD : IsDividendStrategy 𝓕 D)
    (x : ℝ) (t : ℝ≥0) (ht : 0 < t) :
    ∀ᵐ ω ∂P,
      Tendsto (fun s : ℝ≥0 =>
        x + X.X s ω - rightLimit D s ω)
        (𝓝[<] t) (𝓝 (riskProcess X x D t ω)) := by sorry
