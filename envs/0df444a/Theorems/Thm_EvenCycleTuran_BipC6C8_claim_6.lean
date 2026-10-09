-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_6
-- name    : EvenCycleTuran.BipC6C8.claim_6
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:17.150491+00:00
-- url     : https://prove2.me/theorems/2dca6cac-1f6d-4359-9684-fba8cd1d68b0
-- title:
--   Claim 6, p. 15 — g(v₁, v₃) ≤ 4n for every fat pair v₁, v₃
-- statement:
--   Let $G$ be a $C_8$-free bipartite graph on $n$ vertices with classes $A$ and $B$, and let $\{v_1,v_3\}\subseteq A$ be a fat pair. With
--   $$g(v_1,v_3)=\sum_{\substack{\{v_4,v_6\}\subseteq B \text{ fat}\\ v_1,v_3,v_4,v_6 \text{ on a fat } C_6}}|N(v_4,v_6)|$$
--   (the sum over unordered fat pairs of $B$ that lie together with $v_1,v_3$ on a common fat $6$-cycle), we have
--   $$g(v_1,v_3)\le 4n.$$
--
--   This bound, combined with Claim 7, gives the $O(n^{2.5})$ bound on fat $6$-cycles (Claim 8).
--
--   **Formalization Note** The paper calls $g$ "the cardinality of the union" but defines it by the displayed sum, which is what is formalized.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 15, §4.2, definition of g and Claim 6

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_6 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : IsBipartition G A B) (hC8 : EvenCycleTuran.C4Count.CycleFree {8} G)
    (p : Finset V) (hpA : p ⊆ A) (hp : IsFatPair G p) :
    gSum G B p ≤ 4 * Fintype.card V := by sorry

end EvenCycleTuran.BipC6C8
