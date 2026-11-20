-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_pj_reward80g_upper_L1_to_positive_gap
-- name    : AvramDividend.Classical.avram_pj_reward80g_upper_L1_to_positive_gap
-- status  : Open
-- author  : @WillR
-- created : 2026-11-20T00:15:43.087828+00:00
-- url     : https://prove2.me/theorems/cb4c3330-b01f-4c0b-9044-8e4b272c5d42
-- title:
--   Signed upper L1 mesh approximation gives positive reward gap budget
-- statement:
--   Given an integrable stopped reward difference G-U and almost-sure upper domination by the positive part of V-U, a spatial L1 correction K of mass at most epsilon/4 and vanishing integrable upper mesh errors imply a positive-part reward budget epsilon/2. The upper mesh source need not be an equality and does not use an initial-time Q dividend grid defect.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_avram_pj_reward80f_signed_L1_to_positive_gap
open MeasureTheory Set Filter Topology AvramDividend.Classical
noncomputable section

theorem AvramDividend.Classical.avram_pj_reward80g_upper_L1_to_positive_gap
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (G U V : Ω → ℝ) (ε : ℝ) (hε : 0 < ε)
    (hSource : ∃ (K : Ω → ℝ) (E : ℕ → Ω → ℝ),
      Integrable K P ∧ (∫ ω, |K ω| ∂P) ≤ ε / 4 ∧
      (∀ k, Integrable (E k) P) ∧
      (∀ k, ∀ᵐ ω ∂P, V ω - U ω ≤ K ω + E k ω) ∧
      Tendsto (fun k : ℕ => ∫ ω, |E k ω| ∂P)
        Filter.atTop (𝓝 (0 : ℝ)))
    (hGapI : Integrable (fun ω => G ω - U ω) P)
    (hCompare : ∀ᵐ ω ∂P,
      G ω - U ω ≤ max (0 : ℝ) (V ω - U ω)) :
    (∫ ω, max (0 : ℝ) (G ω - U ω) ∂P) ≤ ε / 2 := by sorry
