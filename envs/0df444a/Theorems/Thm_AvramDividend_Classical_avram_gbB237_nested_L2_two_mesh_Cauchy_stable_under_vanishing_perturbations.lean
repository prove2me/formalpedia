-- Prove2me | Theorems.Thm_AvramDividend_Classical_avram_gbB237_nested_L2_two_mesh_Cauchy_stable_under_vanishing_perturbations
-- name    : AvramDividend.Classical.avram_gbB237_nested_L2_two_mesh_Cauchy_stable_under_vanishing_perturbations
-- status  : Proved
-- author  : @WillR
-- created : 2026-11-13T08:35:15.224948+00:00
-- url     : https://prove2.me/theorems/4a301708-c371-4b4d-b147-179041f3b3d0
-- title:
--   Nested integrated-mean-square two-mesh Cauchy convergence survives a vanishing per-mesh L2 perturbation
-- statement:
--   For any two measures and two sequences of real-valued coefficient fields with the stated inner and outer squared integrability, if the first and second fields become arbitrarily close in nested mean square at each mesh and the second fields are two-mesh Cauchy, then the first fields are also two-mesh Cauchy in integrated expected squared energy. This provides the final abstract selected-cutoff-to-fixed-cutoff stability step in the original Gaussian route.
-- source:
--   Root-oriented Gaussian B65 bridge between B220 original selected clipping, B235 nested clipping strip bounds, and B234 upper-only shrinking occupation. Math uses three-term L2 triangle bound and product filter squeeze.

import Mathlib
open MeasureTheory Filter Topology
noncomputable section

theorem AvramDividend.Classical.avram_gbB237_nested_L2_two_mesh_Cauchy_stable_under_vanishing_perturbations
    {α β : Type*} [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β)
    (f g : ℕ → α → β → ℝ)
    (hff : ∀ m p s, Integrable
      (fun ω => (f m s ω - f p s ω)^2) ν)
    (hfg : ∀ m s, Integrable
      (fun ω => (f m s ω - g m s ω)^2) ν)
    (hgg : ∀ m p s, Integrable
      (fun ω => (g m s ω - g p s ω)^2) ν)
    (hffOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (f m s ω - f p s ω)^2 ∂ν) μ)
    (hfgOuter : ∀ m, Integrable
      (fun s => ∫ ω, (f m s ω - g m s ω)^2 ∂ν) μ)
    (hggOuter : ∀ m p, Integrable
      (fun s => ∫ ω, (g m s ω - g p s ω)^2 ∂ν) μ)
    (hClose : Tendsto (fun m =>
      ∫ s, (∫ ω, (f m s ω - g m s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)))
    (hCauchy : Tendsto (fun mp : ℕ × ℕ =>
      ∫ s, (∫ ω, (g mp.1 s ω - g mp.2 s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ))) :
    Tendsto (fun mp : ℕ × ℕ =>
      ∫ s, (∫ ω, (f mp.1 s ω - f mp.2 s ω)^2 ∂ν) ∂μ)
      atTop (𝓝 (0 : ℝ)) := by sorry
