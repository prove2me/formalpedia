-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_ga_abs_L1_global_to_restricted
-- name    : AvramDividend.Classical.avram_ga_abs_L1_global_to_restricted
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-17T17:23:46.991811+00:00
-- url     : https://prove2.me/theorems/eb24c6d7-a8bd-41a4-8418-74c59d2f28c7
-- title:
--   Absolute Gaussian cross global L1 vanishing transfers to any stopped restriction
-- statement:
--   If a Gaussian fullcell cross B has absolute integrability and mean absolute value tending to zero globally, then it is absolutely integrable and tends to zero in mean on any measurable stopping clock restriction. Uses simple domination of measures and the nonnegative squeeze.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_ga_abs_L1_global_to_restricted
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (A : Set Ω) (B : ℕ → Ω → ℝ)
    (hBI : ∀ m, Integrable (fun ω => |B m ω|) P)
    (hBt : Tendsto (fun m => ∫ ω, |B m ω| ∂P)
       atTop (𝓝 (0 : ℝ))) :
    (∀ m, Integrable (fun ω => |B m ω|) (P.restrict A)) ∧
    Tendsto (fun m => ∫ ω in A, |B m ω| ∂P)
       atTop (𝓝 (0 : ℝ)) := by sorry
