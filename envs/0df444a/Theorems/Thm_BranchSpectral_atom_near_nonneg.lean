-- Prove2me | Theorems.Thm_BranchSpectral_atom_near_nonneg
-- name    : BranchSpectral.atom_near_nonneg
-- status  : Open
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:47:20.77018+00:00
-- url     : https://prove2.me/theorems/bbec6b0f-7df0-4cf1-9895-eb78f1bcd1a7
-- title:
--   Nonnegativity of nearby spectral atoms
-- statement:
--   If g>0, |e|≤1/2, t>0 and g≤1/t, then
--   $$e^{-(g^2-e^2)t}\cos(2egt)\ge0.$$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchSpectral.atom_near_nonneg (g e t : ℝ) (hg : 0 < g)
    (he : |e| ≤ 1/2) (ht : 0 < t) (hnear : g ≤ t⁻¹) :
    0 ≤ (fun (g e t : ℝ) => Real.exp (-(g^2-e^2)*t)*Real.cos (2*e*g*t)) g e t := by sorry
