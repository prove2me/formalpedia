-- Prove2me | Theorems.Thm_BranchSpectral_critical_atom_nonneg
-- name    : BranchSpectral.critical_atom_nonneg
-- status  : Open
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:47:34.084509+00:00
-- url     : https://prove2.me/theorems/197767b1-51d1-436f-80c5-d8ce2a861749
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

theorem BranchSpectral.critical_atom_nonneg (g t : ℝ) : 0 ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g 0 t := by sorry
