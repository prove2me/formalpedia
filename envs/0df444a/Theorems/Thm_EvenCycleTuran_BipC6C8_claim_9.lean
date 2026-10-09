-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_9
-- name    : EvenCycleTuran.BipC6C8.claim_9
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:23.343205+00:00
-- url     : https://prove2.me/theorems/41cc0aed-4b1b-41d1-8aae-4d9aaf306b4a
-- title:
--   Claim 9, p. 17 — a marked pair x, y in a nice set S and z ∉ S on a 6-cycle form a good triple
-- statement:
--   Let $G$ be a $C_8$-free bipartite graph with classes $A$ and $B$. Suppose $xv_1yv_2zv_3x$ is a $6$-cycle, the pair $\{x,y\}$ is marked (exactly three common neighbours), $x$ and $y$ belong to a nice set $S$ (a $4$-set $S\subseteq A$ with three common neighbours in $B$), and $z\notin S$. Then $\{x,y,z\}$ is a good triple:
--   $$h(x,y,z)\le 6,$$
--   where $h(x,y,z)$ is the number of $6$-cycles of $G$ containing $x$, $y$ and $z$.
--
--   **Formalization Note** The cycle is an injective map $v:\{0,\dots,5\}\to V$ with $x=v(0)$, $y=v(2)$, $z=v(4)$; $h$ counts unlabelled $6$-cycles (subgraphs isomorphic to $C_6$).
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 17, §4.2, definitions of h, good, nice, marked, and Claim 9

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_9 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : IsBipartition G A B) (hC8 : EvenCycleTuran.C4Count.CycleFree {8} G)
    (v : Fin 6 → V) (hv : IsHexagon G v) (S : Finset V) (hS : IsNice G A B S)
    (hmarked : IsMarked G {v 0, v 2}) (hx : v 0 ∈ S) (hy : v 2 ∈ S) (hz : v 4 ∉ S) :
    hexCount G {v 0, v 2, v 4} ≤ 6 := by sorry

end EvenCycleTuran.BipC6C8
