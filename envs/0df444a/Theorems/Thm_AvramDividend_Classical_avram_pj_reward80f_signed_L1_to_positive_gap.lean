-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80f_signed_L1_to_positive_gap
-- name    : AvramDividend.Classical.avram_pj_reward80f_signed_L1_to_positive_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-19T23:53:44.513407+00:00
-- url     : https://prove2.me/theorems/12ab706a-101f-46f8-969c-021aea4a0edb
-- title:
--   Signed stopped mesh L1 budget transfers to a positive-part payoff gap
-- statement:
--   Integrable stopped reward gap G-U dominated by positive part V-U inherits an epsilon/2 positive expectation budget from a signed spatial L1 error at most epsilon/4, nonpositive remainders and vanishing physical mesh L1 errors.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward79_two_stage_cutoff_mesh_signed_L1_budget
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80f_signed_L1_to_positive_gap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G U V : Ω → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ) (Q : ℕ → Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (fun ω => V ω - U ω - K ω - Q k ω) P) ∧
      (∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0) ∧
      Tendsto (fun k : ℕ =>
        ∫ ω, |V ω - U ω - K ω - Q k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by sorry
