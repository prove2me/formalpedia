-- Prove2me | Theorems.Thm_DerivativeChainContinuation_greedy_rows_classification
-- name    : DerivativeChainContinuation.greedy_rows_classification
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:44:19.463339+00:00
-- url     : https://prove2.me/theorems/5b07e438-3308-495c-b0cf-45cf277c3d92
-- title:
--   Every real nearest-parent history follows one extreme branch
-- statement:
--   Let r be a real row tower, with r_k:Fin(k+1)→ℝ and F_k(X)=∏_(j=0)^k(X-r_k(j)). RealRowStep(r,k) means F_(k+1)′=(k+2)F_k and r_(k+1)(i)≤r_k(i)≤r_(k+1)(i+1) for every i∈Fin(k+1). Thus the full derivative relation as well as interlacing is specified. GreedyRowsTo(r,n,x), for x:ℕ→ℝ, requires x_k to be an entry of r_k for every k≤n and |x_(k+1)-x_k|≤|r_(k+1)(j)-x_k| for every k<n and j∈Fin(k+2). Let n≥1. Assume every r_j is monotone for j≤n and RealRowStep(r,j) for all j<n. If GreedyRowsTo(r,n,x), then either x_k=r_k(0) for every k≤n, or x_k=r_k(k) for every k≤n.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyTower.lean, lines 107-126, SHA-256 8b40116c462af4a8a43ad41639ccc897e8a071b5f6821b4a44f21f48d5c9b196.

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

theorem DerivativeChainContinuation.greedy_rows_classification (r : RealRows) (n : ℕ) (hn : 1≤n)
    (hmono : ∀ j≤n,Monotone (r j)) (hstep : ∀ j<n,RealRowStep r j)
    (x : ℕ → ℝ) (hx : GreedyRowsTo r n x) :
    (∀ k≤n,x k=leftRow r k) ∨ (∀ k≤n,x k=rightRow r k) := by sorry
