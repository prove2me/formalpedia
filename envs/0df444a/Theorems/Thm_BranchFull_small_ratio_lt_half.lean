-- Prove2me | Theorems.Thm_BranchFull_small_ratio_lt_half
-- name    : BranchFull.small_ratio_lt_half
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:44:39.726211+00:00
-- url     : https://prove2.me/theorems/66fa72a6-f6b2-49ea-8ac1-290b64d2bb9c
-- title:
--   Small-time relative tail bound
-- statement:
--   For 0<t≤1/10000,
--   $$ ((t^{-1})^2+t^{-1})\exp(-t^{-1}+(10000+1/4)t)<1/2. $$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchFull.small_ratio_lt_half (t : ℝ) (ht : 0 < t) (hc : t ≤ 1/10000) :
    (fun (t : ℝ) => ((t⁻¹)^2+t⁻¹)*Real.exp (-t⁻¹+(10000+1/4)*t)) t < 1/2 := by sorry
