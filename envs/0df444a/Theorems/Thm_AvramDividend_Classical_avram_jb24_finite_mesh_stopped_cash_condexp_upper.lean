-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_jb24_finite_mesh_stopped_cash_condexp_upper
-- name    : AvramDividend.Classical.avram_jb24_finite_mesh_stopped_cash_condexp_upper
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-11T22:33:55.180494+00:00
-- url     : https://prove2.me/theorems/c4ca54dc-e0a0-4a1c-bcaf-9d25e7d077c2
-- title:
--   Finite stopped cash meshes give an initial conditional HJB upper from two dominated noise limits
-- statement:
--   With a pathwise finite-grid stopped cash upper bound, integrable dominating envelopes for both original noise gains and vanishing cash error, the limit noise witnesses are integrable and initially centred, and the original reward conditional expectation is bounded by initial test value.
-- source:
--   Proved avram_jb23_dominated_two_channel_initial_centering_L1 and avram_a07_condexp_upper_of_two_centered_noises, plus the stopped cash limit comparison bridge.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_jb23_dominated_two_channel_initial_centering_L1
import Theorems.Thm_AvramDividend_Classical_avram_jb24_stopped_cash_limit_upper_from_two_noises
import Theorems.Thm_AvramDividend_Classical_avram_a07_condexp_upper_of_two_centered_noises
open MeasureTheory Set Filter AvramDividend.Classical
open scoped NNReal ENNReal Topology
noncomputable section

theorem AvramDividend.Classical.avram_jb24_finite_mesh_stopped_cash_condexp_upper
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {𝓕 : Filtration ℝ≥0 mΩ}
    (b : ℝ) (F MG MJ BG BJ : Ω → ℝ)
    (G J E : ℕ → Ω → ℝ)
    (hFI : Integrable F P)
    (hGI : ∀ k, Integrable (G k) P)
    (hJI : ∀ k, Integrable (J k) P)
    (hGconv : ∀ᵐ ω ∂P, Tendsto (fun k => G k ω) atTop (𝓝 (MG ω)))
    (hJconv : ∀ᵐ ω ∂P, Tendsto (fun k => J k ω) atTop (𝓝 (MJ ω)))
    (hEconv : ∀ᵐ ω ∂P, Tendsto (fun k => E k ω) atTop (𝓝 (0 : ℝ)))
    (hBG : Integrable BG P) (hBJ : Integrable BJ P)
    (hGdom : ∀ k, ∀ᵐ ω ∂P, ‖G k ω‖ ≤ BG ω)
    (hJdom : ∀ k, ∀ᵐ ω ∂P, ‖J k ω‖ ≤ BJ ω)
    (hGzero : ∀ k, P[G k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hJzero : ∀ k, P[J k | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)))
    (hUpper : ∀ k, ∀ᵐ ω ∂P,
      F ω ≤ b + G k ω + J k ω + E k ω) :
    Integrable MG P ∧ Integrable MJ P ∧
    P[MG | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
    P[MJ | 𝓕.rightCont 0] =ᵐ[P] (fun _ => (0 : ℝ)) ∧
    P[F | 𝓕.rightCont 0] ≤ᵐ[P] (fun _ : Ω => b) := by sorry
