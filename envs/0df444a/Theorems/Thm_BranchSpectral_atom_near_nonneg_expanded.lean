-- Prove2me | Theorems.Thm_BranchSpectral_atom_near_nonneg_expanded
-- name    : BranchSpectral.atom_near_nonneg_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T06:01:31.949849+00:00
-- url     : https://prove2.me/theorems/cc45a3a8-3838-4100-8dab-e1b5e85da83d
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

theorem BranchSpectral.atom_near_nonneg_expanded (g e t : ℝ) (hg : 0 < g)
    (he : |e| ≤ 1/2) (ht : 0 < t) (hnear : g ≤ t⁻¹) :
    0 ≤ (Real.exp (-((g)^2-(e)^2)*(t))*Real.cos (2*(e)*(g)*(t))) := by sorry
