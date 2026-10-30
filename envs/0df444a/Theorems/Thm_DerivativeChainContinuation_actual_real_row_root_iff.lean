-- Prove2me | Theorems.Thm_DerivativeChainContinuation_actual_real_row_root_iff
-- name    : DerivativeChainContinuation.actual_real_row_root_iff
-- status  : Proved
-- author  : @labuka
-- created : 2026-10-26T20:36:11.43663+00:00
-- url     : https://prove2.me/theorems/760d64e2-dabc-4532-979f-e297c845bdbc
-- title:
--   Complete complex zero sets of the actual real derivative rows
-- statement:
--   Let r be a real row tower, with r_k:Fin(k+1)→ℝ and F_k(X)=∏_(j=0)^k(X-r_k(j)). RealRowStep(r,k) means F_(k+1)′=(k+2)F_k and r_(k+1)(i)≤r_k(i)≤r_(k+1)(i+1) for every i∈Fin(k+1). Thus the full derivative relation as well as interlacing is specified. For every n∈ℕ, assume RealRowStep(r,j) for all j<n. Use the real tuple r_n, embedded in ℂ, as the source. Then for every k≤n and every w∈ℂ, p_(r_n) differentiated n-k times vanishes at w if and only if w=r_k(j) for some j∈Fin(k+1). No monotonicity hypothesis on the individual rows is added to this statement.
-- source:
--   Private analytic checkpoint d69f598e254dee1915468fa93b3e33b8e1b5b7d6: research-results/unified-20261025/greedy/RAY_THEOREM.md, SHA-256 0d8a115e7059d0fae02ca0217cd20d64fc1baaf2a83795a4b171fa556be44a57. Local formal commit 7200800a2f88105b736aa292a1ec518302074d94 (not asserted pushed), submission_sync/new_formal/greedy/GreedyActual.lean, lines 18-33, SHA-256 d3ac9fdd06dd387e730b07299cffea9935de88f557ffb857e687a74f824fca1d.

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

theorem DerivativeChainContinuation.actual_real_row_root_iff (r : RealRows) (n : ℕ)
    (hstep : ∀ k<n,RealRowStep r k) (k : ℕ) (hk : k≤n) (w : ℂ) :
    (row (fun i => (r n i : ℂ)) (k+1)).eval w=0 ↔
      ∃ j : Fin (k+1), w=(r k j : ℂ) := by sorry
