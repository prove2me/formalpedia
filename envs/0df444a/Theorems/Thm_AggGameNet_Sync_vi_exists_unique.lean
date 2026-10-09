-- Prove2me | Theorems.Thm_AggGameNet_Sync_vi_exists_unique
-- name    : AggGameNet.Sync.vi_exists_unique
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-09T03:36:29.86134+00:00
-- url     : https://prove2.me/theorems/137e4187-bae6-42c4-b1a1-13c57bfc5370
-- title:
--   Proof of Proposition 1, p. 6 — unique solution of VI(K, φ)
-- statement:
--   Let $N\ge1$. Suppose every player has a nonempty compact convex strategy set $K_i$, the field $F_i$ is continuous on $K_i\times\bar K$, and the induced field $\phi_i(x)=F_i(x_i,\sum_jx_j)$ is strictly monotone on $K=\prod_i K_i$. Then
--
--   $$\exists!\,x^*\in K:\quad\sum_i(x_i-x_i^*)^\top\phi_i(x^*)\ge0\quad\text{for every }x\in K.$$
--
--   The paper establishes this VI fact in the proof of Proposition 1, before identifying VI solutions with Nash equilibria.
-- source:
--   Koshal, Nedić, Shanbhag, Distributed Algorithms for Aggregative Games on Graphs, arXiv:1605.00267v2, proof of Proposition 1, p. 6

import Mathlib
import Definitions.Def_AggGameNet_Sync_Setting

namespace AggGameNet.Sync

open Filter

/-- Proof of Proposition 1, p. 6: the associated VI has a unique solution. -/
theorem vi_exists_unique {N n : ℕ} (hN : 0 < N)
    (K : Fin N → Set (E n)) (F : Fin N → E n → E n → E n)
    (h1 : Assumption1 K F) (h2 : Assumption2 K F) :
    ∃ xs, IsVISol K F xs ∧ ∀ y, IsVISol K F y → y = xs := by sorry

end AggGameNet.Sync
