-- Prove2me | Theorems.Thm_BranchFull_large_ratio_lt_half_expanded
-- name    : BranchFull.large_ratio_lt_half_expanded
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:59:02.336479+00:00
-- url     : https://prove2.me/theorems/dacb7686-3ea4-476f-a249-d650ca6206ad
-- title:
--   Large-time relative tail bound
-- statement:
--   For t≥1/10000,
--   $$ (10^6+t^{-1})\exp(-(10^6-10000-1/4)t)<1/2. $$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchFull.large_ratio_lt_half_expanded (t : ℝ) (ht : 1/10000 ≤ t) :
    ((1000000+(t)⁻¹)*Real.exp (-(1000000-10000-1/4)*(t))) < 1/2 := by sorry
