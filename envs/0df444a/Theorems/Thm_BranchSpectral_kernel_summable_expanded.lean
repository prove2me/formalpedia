-- Prove2me | Theorems.Thm_BranchSpectral_kernel_summable_expanded
-- name    : BranchSpectral.kernel_summable_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:01:00.303141+00:00
-- url     : https://prove2.me/theorems/9d410b6c-594d-4ce7-937c-eee7a044d3a6
-- title:
--   Summability of the signed spectral kernel
-- statement:
--   Let g,e be real sequences with |eⱼ|≤1/2, and fix t>0. If ∑ⱼ exp(-gⱼ²t) is summable, then ∑ⱼ exp(-(gⱼ²-eⱼ²)t)cos(2eⱼgⱼt) is summable.
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.kernel_summable_expanded (g e : ℕ → ℝ) (t : ℝ)
    (he : ∀ j, |e j| ≤ 1/2) (ht : 0 < t)
    (hg : Summable (fun j => (Real.exp (-((g j))^2*(t))))) :
    Summable (fun j => (Real.exp (-(((g j))^2-((e j))^2)*(t))*Real.cos (2*((e j))*((g j))*(t)))) := by sorry
