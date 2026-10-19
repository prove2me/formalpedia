-- Prove2me | Theorems.Thm_ExAnteExPost_RPS_implements_rps_succ
-- name    : ExAnteExPost.RPS.implements_rps_succ
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T06:49:40.789858+00:00
-- url     : https://prove2.me/theorems/b1eb4f84-67b2-429b-97d1-5797f964aa4b
-- title:
--   Proof of Theorem 2, p. 11; Algorithm 3, p. 33 — the implemented allocation is the eating stage plus the weighted recursive allocations
-- statement:
--   Fix an instance with $n \ge 1$ agents, a favorite-good choice rule and an admissible decomposition rule $D$. Let $M'$ be a set of goods, $X = \mathrm{Eating}(M', 1)$ and $X = \sum_k w^k A^k$ the decomposition $D(X)$. Write $Y_T(M')$ for the fractional allocation implemented by $T$ stages of Algorithm 1 started from $M'$. Then for every $T$, every agent $i$ and every good $g$,
--   $$Y_{T+1}(M')_{i,g} = X_{i,g} + \sum_k w^k \, Y_T\Big(M' \setminus \bigcup_{i'} A^k_{i'}\Big)_{i,g} .$$
--
--   This is the recursion of Algorithm 3, line 8, and the expectation identity of the proof of Theorem 2: conditioned on the earlier stages, the expected value of the next stage's bundle is the value of that stage's eating allocation. With the envy-freeness of each eating stage it gives the ex-ante half of Theorem 2 by induction on the number of stages.
-- source:
--   Freeman, Shah, Vaish, Best of Both Worlds: Ex-Ante and Ex-Post Fairness in Resource Allocation, arXiv:2005.14122v1, p. 11, proof of Theorem 2; p. 33, Algorithm 3, line 8

import Mathlib
import Definitions.Def_ExAnteExPost_RPS_Model

namespace ExAnteExPost.RPS
open Finset

variable {N G : Type*} [Fintype N] [DecidableEq N] [Fintype G] [DecidableEq G]

/-- Proof of Theorem 2, p. 11, and Algorithm 3, line 8, p. 33: the fractional allocation
implemented by `T + 1` stages on `M'` is the first eating stage `X` plus the weighted sum, over
the terms `wᵏ Aᵏ` of its decomposition, of the allocations implemented by `T` stages on
`M' \ ⋃ᵢ Aᵏᵢ`. -/
theorem implements_rps_succ [Nonempty N] (I : Instance N G) (pick : PickRule N G)
    (hpick : IsFavoritePick I pick) (D : FracAlloc N G → Decomp N G) (hD : IsBvNOracle D)
    (T : ℕ) (M' : Finset G) (i : N) (g : G) :
    implements (rps pick D (T + 1) M') i g =
      eating pick M' i g + ∑ k, (D (eating pick M')).w k *
        implements (rps pick D T (M' \ univ.biUnion ((D (eating pick M')).A k))) i g := by sorry
end ExAnteExPost.RPS
