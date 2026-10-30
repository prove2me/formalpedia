-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_weighted_last_midpoint
-- name    : DerivativeChainContinuation.positive_weighted_last_midpoint
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:30:30.773373+00:00
-- url     : https://prove2.me/theorems/5fe83b90-a2cd-4aca-a6e2-40aca1af1d81
-- title:
--   A maximal positive weighted root crosses the final quotient midpoint
-- statement:
--   For natural s,k and a real polynomial F, write W_(s,k,F)=sF+kXF′. Let F(X)=∏_(i=0)^(d+1)(X-a_i), where d∈ℕ and 0<a_0≤⋯≤a_(d+1). Let s∈ℕ, k≥1, and t>0 satisfy W_(s,k,F)(t)=0 and x≤t for every positive real root x of W_(s,k,F). If a_d<a_(d+1), then (a_d+a_(d+1))/2≤t.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveWeightedMidpoint.lean, lines 52-102, SHA-256 fd49195c9b702f26f5108e5b108216c827ef1bad045d9690c0953013a444afac.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_PositiveWeightedMidpoint
import Definitions.Def_DerivativeChainContinuation_RealInterlacing
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.positive_weighted_last_midpoint (d s k : ℕ) (a : Fin (d+2) → ℝ)
    (ha : Monotone a) (hpositive : ∀ i,0<a i) (hk : 1≤k)
    (hgap : a (Fin.last d).castSucc<a (Fin.last (d+1)))
    (t : ℝ) (ht : 0<t) (hroot : (positiveWeighted s k (realRootProduct a)).eval t=0)
    (hmax : ∀ x : ℝ,0<x → (positiveWeighted s k (realRootProduct a)).eval x=0 → x≤t) :
    (a (Fin.last d).castSucc+a (Fin.last (d+1)))/2≤t := by sorry
