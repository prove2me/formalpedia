-- Prove2me | Theorems.Thm_AppliedSDE_SarkkaSolin_girsanov_density_preserves_path_continuity
-- name    : AppliedSDE.SarkkaSolin.girsanov_density_preserves_path_continuity
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-14T09:26:06.394018+00:00
-- url     : https://prove2.me/theorems/023ae8f0-c629-413e-951d-29864acb1784
-- title:
--   Any absolutely continuous terminal-density change preserves almost-sure path continuity
-- statement:
--   If a real-valued stochastic process has sample paths continuous in time for almost every outcome under the original measure P, then under any likelihood-weighted measure Q=P.withDensity(rho) the same original process remains almost surely continuous in time. This follows from the absolute continuity Q<<P of a density-weighted measure. It is a necessary path-regularity bridge in Girsanov, allowing Brownian continuity events to transfer to the tilted measure without assuming continuity separately under Q.
-- source:
--   Särkkä and Solin (2019), Applied Stochastic Differential Equations, Chapter 7, Girsanov measure change; Mathlib MeasureTheory.withDensity_absolutelyContinuous.

import Mathlib
open MeasureTheory
open scoped ENNReal

theorem AppliedSDE.SarkkaSolin.girsanov_density_preserves_path_continuity
    {Ω : Type*} [MeasurableSpace Ω]
    (P : Measure Ω) (ρ : Ω → ℝ≥0∞)
    (X : ℝ → Ω → ℝ)
    (hcont : Filter.Eventually
      (fun ω : Ω => Continuous (fun t : ℝ => X t ω)) (ae P)) :
    Filter.Eventually
      (fun ω : Ω => Continuous (fun t : ℝ => X t ω))
      (ae (P.withDensity ρ)) := by
  sorry
