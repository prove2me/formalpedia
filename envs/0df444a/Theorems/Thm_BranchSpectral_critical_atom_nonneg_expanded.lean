-- Prove2me | Theorems.Thm_BranchSpectral_critical_atom_nonneg_expanded
-- name    : BranchSpectral.critical_atom_nonneg_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:02:10.071069+00:00
-- url     : https://prove2.me/theorems/f82db785-ad94-4f05-b6ae-a81efbf5c535
-- title:
--   Nonnegativity of a critical spectral atom
-- statement:
--   For all real g,t,
--   $$e^{-(g^2-0^2)t}\cos(2\cdot0\cdot g t)\ge0.$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.critical_atom_nonneg_expanded (g t : ℝ) : 0 ≤ (Real.exp (-((g)^2-(0)^2)*(t))*Real.cos (2*(0)*(g)*(t))) := by sorry
