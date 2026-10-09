-- Prove2me | Theorems.Thm_AggGameNet_Gossip_vi_exists_unique
-- name    : AggGameNet.Gossip.vi_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T04:34:34.419152+00:00
-- url     : https://prove2.me/theorems/24173838-7f58-4190-891e-8ac3afbcbc66
-- title:
--   Proof of Proposition 1, p. 6 — the variational inequality has a unique solution
-- statement:
--   Let $N\ge1$. Suppose every strategy set $K_i$ is nonempty, compact, and convex, and $F_i$ is continuous on $K_i\times\bar K$. Suppose the game map $\phi(x)_i=F_i(x_i,\sum_jx_j)$ is strictly monotone on $K=\prod_iK_i$. Then
--
--   $$
--   \exists!x^*\in K:\quad \sum_i\langle x_i-x_i^*,\phi_i(x^*)\rangle\ge0
--   \quad\text{for every }x\in K.
--   $$
--
--   This is the existence and uniqueness result used to identify the limit in Proposition 3.
--
--   **Formalization Note** The paper derives these properties from continuously differentiable convex payoffs. The statement takes the continuous map $F$ as primitive, as the convergence theorem uses only $F$ and the variational inequality.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, proof of Proposition 1, p. 6

import Mathlib
import Definitions.Def_AggGameNet_Gossip_Setting

open MeasureTheory Filter Finset
open scoped BigOperators

namespace AggGameNet.Gossip

theorem vi_exists_unique {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (h2 : AggGameNet.Sync.Assumption2 K F) :
    ∃ xs : Fin N → AggGameNet.Sync.E n, IsVISol K F xs ∧
      ∀ y : Fin N → AggGameNet.Sync.E n, IsVISol K F y → y = xs := by sorry

end AggGameNet.Gossip
