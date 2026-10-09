-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_observation_1
-- name    : EvenCycleTuran.BipC6C8.observation_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:21.417984+00:00
-- url     : https://prove2.me/theorems/b1f12061-6d29-4a16-b312-fa0b2c38da20
-- title:
--   Observation 1, p. 15 — (N(v₄, v₆) ∩ N(v₄, v′₆)) ∖ {v₁, v₃} = ∅
-- statement:
--   Let $G$ be a $C_8$-free bipartite graph with classes $A$ and $B$. Suppose $\{v_1,v_3\}\subseteq A$ is a fat pair, $\{v_4,v_6\}$ and $\{v_4,v_6'\}$ are distinct fat pairs (in $B$), and $v_1v_2v_3v_4v_5v_6v_1$ and $v_1v_2'v_3v_4v_5'v_6'v_1$ are fat $6$-cycles. Then
--   $$\bigl(N(v_4,v_6)\cap N(v_4,v_6')\bigr)\setminus\{v_1,v_3\}=\emptyset.$$
--
--   In the proof of Claim 6 this makes the sets $N(v_4,v_6)\setminus\{v_1,v_3\}$ pairwise disjoint over a star of fat pairs centred at $v_4$.
--
--   **Formalization Note** The printed conclusion reads $N(v_4',v_6')$; the hypotheses have $v_4'=v_4$ and the proof writes $N(v_4,v_6')$, which is what is stated here.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 15, §4.2, Observation 1 (in the proof of Claim 6)

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem observation_1 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : IsBipartition G A B) (hC8 : EvenCycleTuran.C4Count.CycleFree {8} G)
    (v w : Fin 6 → V) (hv : IsFatHexagon G v) (hw : IsFatHexagon G w)
    (h0 : w 0 = v 0) (h2 : w 2 = v 2) (h3 : w 3 = v 3) (hA : v 0 ∈ A)
    (hfat13 : IsFatPair G {v 0, v 2}) (hfat46 : IsFatPair G {v 3, v 5})
    (hfat46' : IsFatPair G {v 3, w 5}) (hne : v 5 ≠ w 5) :
    (commonNbrs G {v 3, v 5} ∩ commonNbrs G {v 3, w 5}) \ {v 0, v 2} = ∅ := by sorry

end EvenCycleTuran.BipC6C8
