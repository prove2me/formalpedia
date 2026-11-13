-- Prove2me | Theorems.Thm_DirKECC1549_Main_hitting_set_stabilizes
-- name    : DirKECC1549.Main.hitting_set_stabilizes
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-13T03:54:46.233901+00:00
-- url     : https://prove2.me/theorems/8e9d84a7-569a-4466-a3aa-7b27bc462e14
-- title:
--   Bottom-up threshold propagation stabilizes on a rooted tree
-- statement:
--   Let $V$ have $n$ vertices, let $r$ be a root, and suppose a parent map fixes $r$ and every vertex reaches $r$ under repeated parent steps. Given arbitrary natural vertex weights and a threshold $b$, define Algorithm 2's propagated values by starting with zero at every vertex and repeatedly replacing each value with the vertex weight plus its children's previous values, reset to zero if the sum exceeds $b$. Then every value is unchanged between rounds $n$ and $n+1$. This is a stabilization property of bottom-up propagation on a finite rooted tree, independent of any graph-edge or outdegree assumptions.
-- source:
--   Derived auxiliary fact for Algorithm 2, Georgiadis, Kipouridis, Kosinas, Papadopoulos and Pergaminelis, STOC 2027 submission #1549, Section 3.2.1, pp. 13–14.

import Definitions.Def_DirKECC1549_Main_HittingSet
set_option autoImplicit false

namespace DirKECC1549.Main
theorem hitting_set_stabilizes {n : ℕ} (r : Fin n) (par : Fin n → Fin n)
    (deg : Fin n → ℕ) (b : ℕ) (hroot : par r = r)
    (hreach : ∀ v, ∃ j : ℕ, par^[j] v = r) (v : Fin n) :
    alg2Rho r par deg b (n + 1) v = alg2Rho r par deg b n v := by sorry
end DirKECC1549.Main
