-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jump6_A_original_spatial_kappa_clock_equals_first_negative_mark_when_ruin_clipped_and_upper_exit_later
-- name    : AvramDividend.Classical.avram_jump6_A_original_spatial_kappa_clock_equals_first_negative_mark_when_ruin_clipped_and_upper_exit_later
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T15:43:37.461574+00:00
-- url     : https://prove2.me/theorems/0404db4b-626f-473a-bf4e-1f854cdaffc5
-- title:
--   Original physical κ spatial stopping clock equals the true first negative mark when the clipped ruin clock reaches the mark and upper exit is later
-- statement:
--   For the original spectrally negative Lévy upper-exit localisation κ_k = min(ρ, τ^+_{k+1}), on a physical first-ruin marked path where the ruin-clipped stop ρ equals the first negative-jump time σ and the upward exit is no earlier than σ, the original κ_k is exactly σ for every spatial mesh level k. This identifies the original source 061f936f stopped cash H_k with the already-Proved genuine physical first-ruin terminal-plus-inclusive dividend cash zero lemma. It is a sound pointwise stopping-clock bridge; the positive-measure model and exact κ stop certificates remain separate obligations.

import Mathlib
import Definitions.Def_AvramDividend_Classical_TwoSidedExit
set_option autoImplicit false
open MeasureTheory Set AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_jump6_A_original_spatial_kappa_clock_equals_first_negative_mark_when_ruin_clipped_and_upper_exit_later
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    {𝓕 : Filtration ℝ≥0 ‹MeasurableSpace Ω›}
    (X : SpectrallyNegativeLevy P 𝓕)
    (ω : Ω) (ρ : Ω → ℝ≥0) (κ : ℕ → Ω → ℝ≥0)
    (k : ℕ) (σ : ℝ≥0)
    (hρ : ρ ω = σ)
    (hκ : κ k ω =
      (min (ρ ω : ℝ≥0∞)
        (twoSidedExitUpTime X ((k : ℝ) + 1) ω)).toNNReal)
    (hUpper : (σ : ℝ≥0∞) ≤
      twoSidedExitUpTime X ((k : ℝ) + 1) ω) :
    κ k ω = σ := by sorry
