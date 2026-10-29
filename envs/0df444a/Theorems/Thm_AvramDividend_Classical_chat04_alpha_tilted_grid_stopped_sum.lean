-- Prove2me | Theorems.Thm_AvramDividend_Classical_chat04_alpha_tilted_grid_stopped_sum
-- name    : AvramDividend.Classical.chat04_alpha_tilted_grid_stopped_sum
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-28T23:20:37.332995+00:00
-- url     : https://prove2.me/theorems/0db5c8c2-1ae8-4b37-aa0a-7c501e2fb59e
-- title:
--   Finite-grid alpha-tilted occupation identity at first upcrossing
-- statement:
--   For a real martingale M and an adapted crossing observable Y on a finite grid, the corrected process b^n M_n - (b-1) times its pre-crossing sum is a martingale. Bounded first-upcrossing optional sampling therefore equates its stopped expectation with its initial value. This is the finite-grid alpha-tilted occupation identity needed before the continuous-time Riemann-sum limit.
-- source:
--   Source-faithful child for parent AvramDividend.Classical.chat04_unbounded_stopped_scale_harmonicity_general_reserve (be9dc931-e07f-4a95-8207-11114d0a82ff), isolated from its assigned alpha-tilted pre-upcrossing occupation identity. The source uses the Proved compensated-exponential martingale, deterministic sampled-filtration reindex, martingalePart representation, and Proved bounded first-crossing optional stopping. A separate bridge must instantiate the generic finite-grid result with the Levy exponential and prove the continuous-time occupation limit; publication alone creates neither a parent-child graph edge nor a parent proof.

import Mathlib
import Theorems.Thm_AvramDividend_Classical_chat03_bounded_first_crossing_martingale_identity

open MeasureTheory Set
open AvramDividend.Classical

theorem AvramDividend.Classical.chat04_alpha_tilted_grid_stopped_sum
    {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P]
    {G : Filtration ℕ mΩ} [SigmaFiniteFiltration P G]
    (Y M : ℕ → Ω → ℝ) (hY : Adapted G Y)
    (hM : Martingale M G P) (hMI : ∀ k, Integrable (M k) P)
    (b a : ℝ) (N : ℕ) :
    (∫ ω, b ^ (hittingBtwn Y (Set.Ioi a) 0 N ω) *
        M (hittingBtwn Y (Set.Ioi a) 0 N ω) ω -
      (b - 1) * (∑ k ∈ Finset.range N,
        if k < hittingBtwn Y (Set.Ioi a) 0 N ω then b ^ k * M k ω else 0) ∂P) =
      ∫ ω, M 0 ω ∂P := by sorry
