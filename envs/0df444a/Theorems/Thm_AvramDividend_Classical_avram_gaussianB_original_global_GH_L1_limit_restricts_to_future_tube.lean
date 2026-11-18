-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gaussianB_original_global_GH_L1_limit_restricts_to_future_tube
-- name    : AvramDividend.Classical.avram_gaussianB_original_global_GH_L1_limit_restricts_to_future_tube
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-18T00:36:44.525387+00:00
-- url     : https://prove2.me/theorems/0c70b510-f45c-481c-8536-cc242bd51c03
-- title:
--   Any original globally integrable Gaussian grid L1 limit remains L1 on a measurable future tube
-- statement:
--   For a real-valued globally integrable error sequence between the exact original stopped G/H physical-grid martingale M_m and its candidate limit N, vanishing global L1 error implies vanishing L1 error on any measurable event A, including the positive future-dependent Brownian tube. The theorem does not require the localisation event to be measurable at time zero and therefore bridges the F0 budget restriction of the original fixed-band statement to the positive-probability future Gaussian event used to refute it.

import Mathlib.MeasureTheory.Integral.Bochner.Set
open scoped Topology
open MeasureTheory Filter
noncomputable section

theorem AvramDividend.Classical.avram_gaussianB_original_global_GH_L1_limit_restricts_to_future_tube
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω)
    (M : ℕ → Ω → ℝ) (N : Ω → ℝ)
    (hInt : ∀ m, Integrable (fun ω => |N ω - M m ω|) P)
    (hL1 : Tendsto (fun m => ∫ ω, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)))
    (A : Set Ω) (hA : MeasurableSet A) :
    Tendsto (fun m => ∫ ω in A, |N ω - M m ω| ∂P)
      atTop (𝓝 (0 : ℝ)) := by sorry
