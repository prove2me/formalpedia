-- Prove2me | Theorems.Thm_DerivativeChainContinuation_left_rows_greedy
-- name    : DerivativeChainContinuation.left_rows_greedy
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:46:46.695504+00:00
-- url     : https://prove2.me/theorems/cd6f2c93-83d4-4ec0-92b1-05ed23937ca2
-- title:
--   Smallest roots form an actual nearest-parent row history
-- statement:
--   Let r be a real row tower, with r_k:Fin(k+1)→ℝ and F_k(X)=∏_(j=0)^k(X-r_k(j)). RealRowStep(r,k) means F_(k+1)′=(k+2)F_k and r_(k+1)(i)≤r_k(i)≤r_(k+1)(i+1) for every i∈Fin(k+1). Thus the full derivative relation as well as interlacing is specified. GreedyRowsTo(r,n,x), for x:ℕ→ℝ, requires x_k to be an entry of r_k for every k≤n and |x_(k+1)-x_k|≤|r_(k+1)(j)-x_k| for every k<n and j∈Fin(k+2). For every n∈ℕ, assume every r_j is monotone for j≤n and RealRowStep(r,j) for every j<n. Then the history x_k=r_k(0) satisfies GreedyRowsTo(r,n,x).
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyTower.lean, lines 88-105, SHA-256 8b40116c462af4a8a43ad41639ccc897e8a071b5f6821b4a44f21f48d5c9b196.

import Mathlib
import Definitions.Def_DerivativeChainContinuation_GreedyReal
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

theorem DerivativeChainContinuation.left_rows_greedy (r : RealRows) (n : ℕ)
    (hmono : ∀ j≤n,Monotone (r j)) (hstep : ∀ j<n,RealRowStep r j) :
    GreedyRowsTo r n (leftRow r) := by sorry
