-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_bv_excess22_original_source_collision_lintegral_vanish
-- name    : AvramDividend.Classical.avram_bv_excess22_original_source_collision_lintegral_vanish
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-09T21:39:29.450639+00:00
-- url     : https://prove2.me/theorems/2811485c-fbce-44ca-877b-1fc399d3d3b4
-- title:
--   Finite-BV original-count collision excess vanishes in expected mass under genuine occupied-cell refinement
-- statement:
--   For the actual original BV negative-jump count N_T and finite uniform-grid occupied count K_n, the proved original fine-grid one-jump separation makes K_n eventually equal N_T almost surely. The source exact Levy first moment makes N_T integrable. This source-collision-limit interface shows the total overcount N_T-K_n tends to zero in L1, using pinned Mathlib ENNReal dominated convergence, and requires only measurability of that exact difference. In the 4f605d76 physical error, each positive excess (number of jumps in cell minus one) is precisely this mass. No second moment, arbitrary-grid convergence or global generator B integrability.

import Mathlib
open MeasureTheory Filter Topology
open scoped ENNReal

theorem AvramDividend.Classical.avram_bv_excess22_original_source_collision_lintegral_vanish
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω)
    (K : ℕ → Ω → ℝ≥0∞) (N : Ω → ℝ≥0∞)
    (hDiffMeas : ∀ m, Measurable (fun ω => N ω - K m ω))
    (hInt : (∫⁻ ω, N ω ∂P) < ⊤)
    (hEvent : ∀ᵐ ω ∂P, ∀ᶠ m in (Filter.atTop : Filter ℕ),
      K m ω = N ω) :
    Filter.Tendsto (fun m => ∫⁻ ω, N ω - K m ω ∂P)
      Filter.atTop (nhds (0 : ℝ≥0∞)) := by sorry
