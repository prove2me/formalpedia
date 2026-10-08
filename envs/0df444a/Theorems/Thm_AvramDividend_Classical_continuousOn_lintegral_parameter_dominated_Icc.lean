-- Prove2me | Theorems.Thm_AvramDividend_Classical_continuousOn_lintegral_parameter_dominated_Icc
-- name    : AvramDividend.Classical.continuousOn_lintegral_parameter_dominated_Icc
-- status  : Proved
-- author  : @WillR
-- created : 2026-10-07T23:36:53.732647+00:00
-- url     : https://prove2.me/theorems/ce0b4e8f-3b32-46ae-b5bd-463684b0c422
-- title:
--   Dominated parameter-dependent integrals are continuous on a closed parameter interval
-- statement:
--   Let ν be a measure and F(θ,y) a measurable real integrand for parameters θ in a compact interval [a,b]. If a common integrable real bound dominates |F(θ,y)| for all interval parameters and F is continuous in its interval parameter at almost every y, then θ↦∫F(θ,y)dν is continuous on [a,b]. This is the exact dominated convergence mechanism needed to establish continuity of the canonical Lévy–Khintchine jump integral in the Laplace parameter.
-- source:
--   Pinned Mathlib MeasureTheory.continuous_of_dominated and continuousOn_iff_continuous_restrict.

import Mathlib
open MeasureTheory Set

theorem AvramDividend.Classical.continuousOn_lintegral_parameter_dominated_Icc
    (ν : Measure ℝ) (a b : ℝ) (F : ℝ → ℝ → ℝ) (bound : ℝ → ℝ)
    (hmeas : ∀ θ ∈ Icc a b, AEStronglyMeasurable (F θ) ν)
    (hbound : ∀ θ ∈ Icc a b, ∀ᵐ y : ℝ ∂ν, ‖F θ y‖ ≤ bound y)
    (hboundInt : Integrable bound ν)
    (hcont : ∀ᵐ y : ℝ ∂ν, Continuous (fun z : Icc a b => F z.1 y)) :
    ContinuousOn (fun θ : ℝ => ∫ y : ℝ, F θ y ∂ν) (Icc a b) := by sorry
