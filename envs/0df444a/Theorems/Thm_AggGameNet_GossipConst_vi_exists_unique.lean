-- Prove2me | Theorems.Thm_AggGameNet_GossipConst_vi_exists_unique
-- name    : AggGameNet.GossipConst.vi_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T05:32:06.356059+00:00
-- url     : https://prove2.me/theorems/3151efdb-7e3a-432f-81e2-b822222a2ead
-- title:
--   Proof of Proposition 4 — unique VI solution
-- statement:
--   Suppose $N\ge1$, each strategy set $K_i$ is nonempty compact and convex, the aggregate map $\phi$ is continuous on $K$, and $\phi$ is strongly monotone there with modulus $\mu>0$. Then
--
--   $$\exists!x^*\in K:\quad \sum_i\langle x_i-x_i^*,\phi(x^*)_i\rangle\ge0\quad\text{for every }x\in K.$$
--
--   This supplies the equilibrium point used in Proposition 4. **Formalization Note** The continuity condition is expressed through the component maps $F_i$ in Assumption 1.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, proof of Proposition 4, p. 26

import Mathlib
import Definitions.Def_AggGameNet_GossipConst_Game

namespace AggGameNet.GossipConst

theorem vi_exists_unique {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (AggGameNet.Sync.E n)) (F : Fin N → AggGameNet.Sync.E n → AggGameNet.Sync.E n → AggGameNet.Sync.E n)
    (h1 : AggGameNet.Sync.Assumption1 K F) (mu : ℝ) (hmu : 0 < mu)
    (hsm : StronglyMonotone K F mu) :
    ∃ xs, AggGameNet.Gossip.IsVISol K F xs ∧ ∀ y, AggGameNet.Gossip.IsVISol K F y → y = xs := by sorry

end AggGameNet.GossipConst
