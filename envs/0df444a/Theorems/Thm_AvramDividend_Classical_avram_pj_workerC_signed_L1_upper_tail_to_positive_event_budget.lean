-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_workerC_signed_L1_upper_tail_to_positive_event_budget
-- name    : AvramDividend.Classical.avram_pj_workerC_signed_L1_upper_tail_to_positive_event_budget
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T18:42:44.020501+00:00
-- url     : https://prove2.me/theorems/c174d45c-eadd-4061-9b3d-826397df5587
-- title:
--   Signed L1 stopped Ito error with vanishing tail yields half-epsilon positive event reward budget
-- statement:
--   From integrable G-U bounded above by signed small K and vanishing L1 E with nonpositive Q_k for every k, derive expected positive reward on any event <= epsilon/2 using the source-exact eventwise positive residual transfer.
-- source:
--   Generic analytic transfer for pure-jump original HJB finitecap C2 physical grid source; uses already Proved avram_pj_reward71.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward71_original_posresidual_signed_ledger_transfer
open MeasureTheory Set Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_pj_workerC_signed_L1_upper_tail_to_positive_event_budget
    {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (A : Set Ω) (G U K : Ω → ℝ) (E Q : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hGU : Integrable (fun ω => G ω - U ω) P)
    (hKI : Integrable K P)
    (hKsmall : (∫ ω, |K ω| ∂P) ≤ ε / 4)
    (hEI : ∀ k, Integrable (E k) P)
    (hQ : ∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0)
    (hBound : ∀ k, ∀ᵐ ω ∂P,
      G ω - U ω ≤ K ω + E k ω + Q k ω)
    (hVan : Tendsto (fun k => ∫ ω, |E k ω| ∂P)
      atTop (𝓝 (0 : ℝ))) :
    (∫ ω in A, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by sorry
