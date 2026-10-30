-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_weighted_single_radius
-- name    : DerivativeChainContinuation.positive_weighted_single_radius
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:34:47.912555+00:00
-- url     : https://prove2.me/theorems/57b11788-0447-44b9-91e8-11bd340859d4
-- title:
--   A single-radius quotient satisfies b < 2^k t
-- statement:
--   For natural s,k and a real polynomial F, write W_(s,k,F)=sF+kXF′. For natural s,k with k≥2 and real b,t with t>0, if W_(s,k,X-b)(t)=0, then b<2^k t. No separate hypothesis b>0 or s>0 is imposed.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveWeightedExtreme.lean, lines 38-60, SHA-256 eb30e63dfdb9ea1b188136c3a6c2407b2fbc523ebeb1dc7bf84312c26d51491b.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_weighted_single_radius (s k : ℕ) (hk : 2 ≤ k) (b t : ℝ)
    (ht : 0<t)
    (hroot : (positiveWeighted s k (X-C b)).eval t=0) : b<(2 : ℝ)^k*t := by sorry
