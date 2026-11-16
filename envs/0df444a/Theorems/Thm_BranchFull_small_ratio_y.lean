-- Prove2me | Theorems.Thm_BranchFull_small_ratio_y
-- name    : BranchFull.small_ratio_y
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:44:26.787989+00:00
-- url     : https://prove2.me/theorems/67d05827-dbe0-4057-911e-6db62d4783a8
-- title:
--   Small-time exponential tail after inversion
-- statement:
--   For real y ≥ 10000,
--   $$ (y^2+y)\exp(-y+(10000+1/4)/y)<1/2. $$
--   Scope: the explicit hypotheses of this theorem only. No proof of RH or of higher tower-diagonal positivity is claimed.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib
open MeasureTheory Set Filter Topology

theorem BranchFull.small_ratio_y (y : ℝ) (hy : 10000 ≤ y) :
    (y^2+y) * Real.exp (-y+(10000+1/4)/y) < 1/2 := by sorry
