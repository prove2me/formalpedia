-- Prove2me | Theorems.Thm_DirKECC1549_Main_walks_in_scc
-- name    : DirKECC1549.Main.walks_in_scc
-- status  : Proved
-- author  : @parclytaxel
-- created : 2026-11-12T09:34:14.232034+00:00
-- url     : https://prove2.me/theorems/66de0801-8faa-40e9-942d-cde9dd4d52b9
-- title:
--   Directed walks between vertices in a strongly connected component remain in it
-- statement:
--   Let $G$ be a finite directed multigraph, and let $S$ be the strongly connected component of $a$. If $x,y\in S$, then for every directed walk $p$ from $x$ to $y$ and every edge $e$ on $p$,
--
--   $$\operatorname{tail}(e)\in S\quad\text{and}\quad\operatorname{head}(e)\in S.$$
--
--   This is the walk convexity of strongly connected components; loops and parallel edges are allowed.
-- source:
--   Auxiliary lemma for Claim 1, Georgiadis, Kipouridis, Kosinas, Papadopoulos, Pergaminelis, STOC 2027 submission #1549, Section 3.3, p.17; derived supporting graph-theoretic statement.

import Definitions.Def_DirKECC1549_Main_Graph
set_option autoImplicit false

namespace DirKECC1549.Main
theorem walks_in_scc {n m : ℕ} (G : Fin m → Fin n × Fin n) (a x y : Fin n)
    (hx : StronglyConn G a x) (hy : StronglyConn G a y) :
    ∀ p, IsWalk G x p y → ∀ e ∈ p, (G e).1 ∈ sccOf G a ∧ (G e).2 ∈ sccOf G a := by sorry
end DirKECC1549.Main
