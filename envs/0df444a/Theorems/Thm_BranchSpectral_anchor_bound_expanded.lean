-- Prove2me | Theorems.Thm_BranchSpectral_anchor_bound_expanded
-- name    : BranchSpectral.anchor_bound_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:02:43.797287+00:00
-- url     : https://prove2.me/theorems/c40ac212-ca35-47b2-bd2f-05be16420316
-- title:
--   Lower bound from one low critical atom
-- statement:
--   For 0<g≤100 and t>0, the critical atom satisfies
--   $$e^{-10000t}\le e^{-g^2t}.$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.anchor_bound_expanded (g t : ℝ) (hg : 0 < g) (h100 : g ≤ 100) (ht : 0 < t) :
    Real.exp (-10000*t) ≤ (Real.exp (-((g)^2-(0)^2)*(t))*Real.cos (2*(0)*(g)*(t))) := by sorry
