-- Prove2me | Theorems.Thm_DerivativeChainContinuation_positive_weighted_outer_midpoint
-- name    : DerivativeChainContinuation.positive_weighted_outer_midpoint
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T23:32:35.671499+00:00
-- url     : https://prove2.me/theorems/ccecf7cc-e4a0-450f-8e74-8a36c1ea5570
-- title:
--   The weighted quotient midpoint estimate includes repeated outer roots
-- statement:
--   For natural s,k and a real polynomial F, write W_(s,k,F)=sF+kXF′. Let F(X)=∏_(i=0)^(d+1)(X-a_i), where d∈ℕ and 0<a_0≤⋯≤a_(d+1). Let s∈ℕ, k≥1, and t>0 satisfy W_(s,k,F)(t)=0 and x≤t for every positive real root x of W_(s,k,F). Without requiring distinct outer values, (a_d+a_(d+1))/2≤t.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/positive/PositiveWeightedExtreme.lean, lines 7-29, SHA-256 eb30e63dfdb9ea1b188136c3a6c2407b2fbc523ebeb1dc7bf84312c26d51491b.

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

theorem DerivativeChainContinuation.positive_weighted_outer_midpoint (d s k : ℕ) (a : Fin (d+2) → ℝ)
    (ha : Monotone a) (hpositive : ∀ i,0<a i) (hk : 1 ≤ k)
    (t : ℝ) (ht : 0<t) (hroot : (positiveWeighted s k (realRootProduct a)).eval t=0)
    (hmax : ∀ x : ℝ,0<x → (positiveWeighted s k (realRootProduct a)).eval x=0 → x ≤ t) :
    (a (Fin.last d).castSucc+a (Fin.last (d+1)))/2 ≤ t := by sorry
