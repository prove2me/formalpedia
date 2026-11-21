-- Prove2me | Theorems.Thm_BFWFluidLimit_scaled_variance_hasDerivAt
-- name    : BFWFluidLimit.scaled_variance_hasDerivAt
-- status  : Proved
-- author  : @wfe2017
-- created : 2026-11-20T11:13:07.831955+00:00
-- url     : https://prove2.me/theorems/792d042f-fd62-4bb1-882b-a7b84cc5141c
-- title:
--   Lemma F.2: derivative of scaled own-price variance
-- statement:
--   Suppose t≠0 and u,w have derivatives (p−u(t))/t and (p²−w(t))/t at t. Then the derivative of s↦s(w(s)−u(s)²) at t is (p−u(t))². This is the scalar differential identity in Lemma F.2 of the paper, from which the own-price variance floor follows.
-- source:
--   J. Baek, V. F. Farias, F. Wu, Misspecified Estimate-then-Optimize Leads to Supra-Competitive Prices, arXiv:2605.16064v2, https://arxiv.org/pdf/2605.16064; Lemma F.2 p. 49.

import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.Deriv.MeanValue
import Mathlib.Topology.MetricSpace.Lipschitz
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.SplitIfs

namespace BFWFluidLimit
theorem scaled_variance_hasDerivAt (u w : ℝ → ℝ) (t p : ℝ) (ht : t ≠ 0)
    (hu : HasDerivAt u ((p - u t) / t) t)
    (hw : HasDerivAt w ((p ^ 2 - w t) / t) t) :
    HasDerivAt (fun s => s * (w s - u s ^ 2)) ((p - u t) ^ 2) t := by sorry
end BFWFluidLimit
