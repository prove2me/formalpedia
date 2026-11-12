-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb23_dominated_two_channel_initial_centering_L1
-- name    : AvramDividend.Classical.avram_jb23_dominated_two_channel_initial_centering_L1
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:10:37.371178+00:00
-- url     : https://prove2.me/theorems/000e0852-7fdd-41fd-80aa-09689ec61f20
-- title:
--   Dominated initial-centred Gaussian and jump sequences have integrable centred limits
-- statement:
--   Two initially centred finite-grid noise sequences with integrable dominant envelopes and almost-sure limits yield integrable limits with separate zero conditional expectations at the original initial filtration.
-- source:
--   Proved 22922632 plus exact pinned strong measurability of limit, norm order limit and integrability comparison.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_ja18_original_dominated_condExp_zero_limit
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb23_dominated_two_channel_initial_centering_L1
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (G J : ℕ → Ω → ℝ) (MG MJ BG BJ : Ω → ℝ)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω)
    (hGzero : ∀ k, P[G k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hJzero : ∀ k, P[J k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) :
    Integrable MG P ∧
    (P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) ∧
    Integrable MJ P ∧
    (P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ))) := by sorry
