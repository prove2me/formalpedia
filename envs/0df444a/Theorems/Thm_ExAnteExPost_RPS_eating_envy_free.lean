-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_eating_envy_free
-- name    : ExAnteExPost.RPS.eating_envy_free
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:38.694766+00:00
-- url     : https://prove2.me/theorems/09a27727-cfe3-4b16-8292-31159cde5770
-- title:
--   Proof of Theorem 2, p. 11 — the partial fractional allocation of each eating stage is envy-free
-- statement:
--   Fix an instance and a favorite-good choice rule, so that at every moment each agent eats her most preferred available good. For every set of goods $M'$, the partial fractional allocation $X = \mathrm{Eating}(M', 1)$ is envy-free:
--   $$v_i(X_i) \ge v_i(X_h) \quad \text{for all agents } i, h .$$
--
--   This is the per-stage fact behind the ex-ante half of Theorem 2: the allocation Algorithm 1 implements is the sum of the stage allocations $X^t$ averaged over the earlier draws.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 11, proof of Theorem 2

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- Proof of Theorem 2, p. 11: the partial fractional allocation of one eating stage is
envy-free. -/
theorem eating_envy_free [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (M' : Finset G) : IsEF I (eating pick M') := by sorry
end ExAnteExPost.RPS
