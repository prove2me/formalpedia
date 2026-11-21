-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80h_positiveclock_upper_L1_to_gap
-- name    : AvramDividend.Classical.avram_pj_reward80h_positiveclock_upper_L1_to_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:44:17.889469+00:00
-- url     : https://prove2.me/theorems/ad82dc2a-a49f-40e6-8b3e-f112ca000dbc
-- title:
--   Positive-clock signed L1 physical source and exact zero-clock reward imply whole-clock expected positive gap
-- statement:
--   On strictly positive original stopped clocks, a signed L1 upper source with small spatial correction and vanishing physical-grid errors controls the positive reward gap. At zero stopped clock, exact reward normalisation G=U completes the bound without inserting a spurious initial right-dividend mesh Q. Full negative-mark compensation remains encoded in the signed upper source.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80h_positiveclock_upper_L1_to_gap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (ρ : Ω → ℝ≥0) (G U V : Ω → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, 0 < ρ ω → V ω - U ω ≤ K ω + E k ω) ∧
      Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hZero : ∀ᵐ ω ∂P, ρ ω = 0 → G ω = U ω)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P, 0 < ρ ω →
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by sorry
