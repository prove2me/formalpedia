-- Prove2me | Theorems.Thm_DerivativeChainContinuation_tower_centroid
-- name    : DerivativeChainContinuation.tower_centroid
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:51:21.618526+00:00
-- url     : https://prove2.me/theorems/631b382c-7897-4902-9695-f569447c7ab1
-- title:
--   The linear-row root is the source centroid
-- statement:
--   Let r be a real row tower, with r_k:Fin(k+1)→ℝ and F_k(X)=∏_(j=0)^k(X-r_k(j)). RealRowStep(r,k) means F_(k+1)′=(k+2)F_k and r_(k+1)(i)≤r_k(i)≤r_(k+1)(i+1) for every i∈Fin(k+1). Thus the full derivative relation as well as interlacing is specified. For every n∈ℕ, if RealRowStep(r,j) for every j<n, then Σ_(i=0)^n r_n(i)=(n+1)r_0(0). No row-monotonicity or centering hypothesis is required.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyTower.lean, lines 11-25, SHA-256 8b40116c462af4a8a43ad41639ccc897e8a071b5f6821b4a44f21f48d5c9b196.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_RealTower
import Definitions.Def_DerivativeChainPrivate_foundations
set_option autoImplicit false
set_option backward.isDefEq.respectTransparency false
set_option maxHeartbeats 1600000
open Polynomial DerivativeChainPrivate
namespace DerivativeChainContinuation
end DerivativeChainContinuation
open DerivativeChainContinuation
open scoped BigOperators

theorem DerivativeChainContinuation.tower_centroid (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) :
    ∑ i,r n i = (n+1 : ℝ)*r 0 0 := by sorry
