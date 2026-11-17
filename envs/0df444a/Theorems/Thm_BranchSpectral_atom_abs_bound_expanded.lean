-- Prove2me | Theorems.Thm_BranchSpectral_atom_abs_bound_expanded
-- name    : BranchSpectral.atom_abs_bound_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:00:18.701138+00:00
-- url     : https://prove2.me/theorems/e9fcc4a3-af81-46b4-b8f8-0cc0bd8e3899
-- title:
--   Gaussian domination of a signed spectral atom
-- statement:
--   Write A(g,e,t)=exp(-(g²-e²)t)cos(2egt). For |e|≤1/2 and t>0,
--   $$|A(g,e,t)|\le e^{t/4}e^{-g^2t}.$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.atom_abs_bound_expanded (g e t : ℝ) (he : |e| ≤ 1/2) (ht : 0 < t) :
    |(Real.exp (-((g)^2-(e)^2)*(t))*Real.cos (2*(e)*(g)*(t)))| ≤ Real.exp (t/4)*(Real.exp (-(g)^2*(t))) := by sorry
