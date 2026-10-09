-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_4
-- name    : EvenCycleTuran.BipC6C8.claim_4
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:38.509715+00:00
-- url     : https://prove2.me/theorems/822dcf6f-95c5-436d-86be-eff62bd34342
-- title:
--   Claim 4, p. 14 — two fat 6-cycles sharing the fat pair v₁, v₃ have intersecting fat pairs {v₄, v₆}, {v′₄, v′₆}
-- statement:
--   Let $G$ be a $C_8$-free bipartite graph with classes $A$ and $B$. Let $v_1v_2v_3v_4v_5v_6v_1$ and $v_1v_2'v_3v_4'v_5'v_6'v_1$ be fat $6$-cycles sharing the vertices $v_1,v_3$, and suppose $\{v_1,v_3\}$ is a fat pair. Then
--   $$\{v_4,v_6\}\cap\{v_4',v_6'\}\neq\emptyset.$$
--
--   By Claim 3, $\{v_4,v_6\}$ and $\{v_4',v_6'\}$ are the fat pairs of the two cycles in the other class, so all fat pairs of the other class that appear with $\{v_1,v_3\}$ on a fat $6$-cycle pairwise intersect.
--
--   **Formalization Note** The paper's hypotheses "the cycles are different" and "$\{v_4,v_6\}$, $\{v_4',v_6'\}$ are the other fat pairs" are not assumed: the first only excludes a case where the conclusion is trivial, the second follows from Claim 3.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 14, §4.2, Claim 4 and the sentence before it

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_4 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : IsBipartition G A B) (hC8 : EvenCycleTuran.C4Count.CycleFree {8} G)
    (v w : Fin 6 → V) (hv : IsFatHexagon G v) (hw : IsFatHexagon G w)
    (h0 : w 0 = v 0) (h2 : w 2 = v 2) (hfat : IsFatPair G {v 0, v 2}) :
    (({v 3, v 5} : Finset V) ∩ {w 3, w 5}).Nonempty := by sorry

end EvenCycleTuran.BipC6C8
