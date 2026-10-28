-- Prove2me | Theorems.Thm_FeynmanKac_path_start_ae
-- name    : FeynmanKac.path_start_ae
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-26T21:50:27.266297+00:00
-- url     : https://prove2.me/theorems/fe980805-17e5-4aec-b642-7edf9219bf40
-- title:
--   Diffusion begins at its deterministic initial state
-- statement:
--   Show that the first coordinate of the vector SDE at elapsed time zero agrees almost surely with its deterministic initial state. This uses the genuine IsDiffusion initial-version property and the initial-coordinate condition of the model, together with the identity s=t so elapsed time is zero.
-- source:
--   Canonical SDE initial-value property; accepted IsDiffusion interface https://prove2.me/theorems/7af98979-05ab-4014-86ce-c2315b88e573

import Definitions.Def_FeynmanKac_BoundedDiffusionModel
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic

theorem FeynmanKac.path_start_ae
    {Ω : Type*} [MeasurableSpace Ω]
    (P : MeasureTheory.Measure Ω) [MeasureTheory.IsProbabilityMeasure P]
    (m : FeynmanKac.BoundedDiffusionModel P) :
    (fun ω => m.path m.initialTime ω) =ᵐ[P]
      (fun _ => m.initialState) := by sorry
