-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80i_nonpositive_signed_mesh_L1_to_positive_gap
-- name    : AvramDividend.Classical.avram_pj_reward80i_nonpositive_signed_mesh_L1_to_positive_gap
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-20T07:44:43.902232+00:00
-- url     : https://prove2.me/theorems/45a25082-2cc6-4a14-912c-04928c6f7464
-- title:
--   Nonpositive original physical-grid right-payment mesh, signed L1 convergence, expected positive stopped reward gap
-- statement:
--   If the exact original stopped signed reward has an integrable spatial correction with arbitrarily small L1 norm, the physical-grid signed residual converges to zero in L1, and all genuine pre-ruin discounted right-dividend mesh corrections are nonpositive, then the expected positive original stopped reward gap is small. No additional Markov or Gaussian assumption is introduced.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
open scoped NNReal ENNReal
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80i_nonpositive_signed_mesh_L1_to_positive_gap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G U V : Ω → ℝ) (Q : ℕ → Ω → ℝ)
    (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (fun ω => V ω - U ω - K ω - Q k ω) P) ∧
      Tendsto (fun k : ℕ =>
        ∫ ω, |V ω - U ω - K ω - Q k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hQ : ∀ k, ∀ᵐ ω ∂P, Q k ω ≤ 0)
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by sorry
