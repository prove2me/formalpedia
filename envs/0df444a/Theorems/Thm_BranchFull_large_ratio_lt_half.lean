-- Prove2me | Theorems.Thm_BranchFull_large_ratio_lt_half
-- name    : BranchFull.large_ratio_lt_half
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:45:40.651189+00:00
-- url     : https://prove2.me/theorems/df29f91a-9c0c-4d11-97f8-9a91262b750c
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

theorem BranchFull.large_ratio_lt_half (t : ℝ) (ht : 1/10000 ≤ t) :
    (fun (t : ℝ) => (1000000+t⁻¹)*Real.exp (-(1000000-10000-1/4)*t)) t < 1/2 := by sorry
