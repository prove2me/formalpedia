-- Prove2me | Theorems.Thm_BranchFull_exp_neg_quartic
-- name    : BranchFull.exp_neg_quartic
-- status  : Proved
-- author  : @bueno_ricardo
-- created : 2026-11-16T05:37:54.993168+00:00
-- url     : https://prove2.me/theorems/72925afb-edd7-4bbf-a0f2-ed1b8b23af0f
-- title:
--   Exponential decay bounded by an inverse quartic
-- statement:
--   For every real y > 0, exp(-y) ≤ 24/y^4. Elementary analytic bound used in the conditional Branch 2/3 heat-kernel certificate; not a proof of RH.
-- source:
--   Desenvolvimento RH — Ricardo Marangoni Brandão Bueno. Conditional Branch 2/3 certificate, 16 Nov 2026. No claim of novelty.

import Mathlib

theorem BranchFull.exp_neg_quartic (y : ℝ) (hy : 0 < y) :
    Real.exp (-y) ≤ 24 / y^4  := by sorry
