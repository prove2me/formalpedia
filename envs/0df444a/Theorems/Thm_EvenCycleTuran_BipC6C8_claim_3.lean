-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_3
-- name    : EvenCycleTuran.BipC6C8.claim_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:12.624983+00:00
-- url     : https://prove2.me/theorems/f0b77a6d-0f54-4228-93d8-5915351d6a2c
-- title:
--   Claim 3, p. 14 — if v₁, v₃ is fat on a 6-cycle, neither v₂, v₄ nor v₂, v₆ is fat
-- statement:
--   Let $G$ be a $C_8$-free bipartite graph with classes $A$ and $B$, and let $v_1v_2v_3v_4v_5v_6v_1$ be a $6$-cycle of $G$ such that $\{v_1,v_3\}$ is a fat pair (at least four common neighbours). Then
--   $$\{v_2,v_4\}\text{ is not fat}\quad\text{and}\quad\{v_2,v_6\}\text{ is not fat}.$$
--
--   Consequently a $6$-cycle with fat pairs in both classes has, up to relabelling, exactly the fat pairs $\{v_1,v_3\}$ and $\{v_4,v_6\}$, which is the shape used by all later claims.
--
--   **Formalization Note** The cycle is an injective map $v:\{0,\dots,5\}\to V$ with $v_i$ adjacent to $v_{i+1 \bmod 6}$; the paper's $v_1,\dots,v_6$ are $v(0),\dots,v(5)$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 14, §4.2, Claim 3

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_3 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : IsBipartition G A B) (hC8 : EvenCycleTuran.C4Count.CycleFree {8} G)
    (v : Fin 6 → V) (hv : IsHexagon G v) (hfat : IsFatPair G {v 0, v 2}) :
    ¬ IsFatPair G {v 1, v 3} ∧ ¬ IsFatPair G {v 1, v 5} := by sorry

end EvenCycleTuran.BipC6C8
