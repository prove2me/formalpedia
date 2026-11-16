-- Prove2me | Theorems.Thm_BranchFull_heat_lower_bound_expanded
-- name    : BranchFull.heat_lower_bound_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:59:37.59367+00:00
-- url     : https://prove2.me/theorems/2e7ec007-9f9e-4af0-934c-bcb940db2766
-- title:
--   Two ranges imply a positive heat-kernel bound
-- statement:
--   Let K be a real function. Define rₛ(t)=((t⁻¹)²+t⁻¹)exp(-t⁻¹+(10000+1/4)t) and rₗ(t)=(10⁶+t⁻¹)exp(-(10⁶-10000-1/4)t). Assume K(t)≥exp(-10000t)(1-rₛ(t)) for 0<t≤1/10000 and K(t)≥exp(-10000t)(1-rₗ(t)) for t≥1/10000. Then
--   $$K(t)>\tfrac12 e^{-10000t}\quad(t>0).$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchFull.heat_lower_bound_expanded (K : ℝ → ℝ)
    (hs : ∀ t > 0, t ≤ 1/10000 →
      Real.exp (-10000*t)*(1-((((t)⁻¹)^2+(t)⁻¹)*Real.exp (-(t)⁻¹+(10000+1/4)*(t)))) ≤ K t)
    (hl : ∀ t > 0, 1/10000 ≤ t →
      Real.exp (-10000*t)*(1-((1000000+(t)⁻¹)*Real.exp (-(1000000-10000-1/4)*(t)))) ≤ K t) :
    ∀ t > 0, (1/2)*Real.exp (-10000*t) < K t := by sorry
