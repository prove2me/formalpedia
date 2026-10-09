-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_7
-- name    : EvenCycleTuran.BipC6C8.claim_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:44.011763+00:00
-- url     : https://prove2.me/theorems/91b917b8-d7e4-43dd-818f-03d19038765d
-- title:
--   Claim 7, p. 16 — the hypergraph 𝓗 of neighbourhoods of fat pairs on fat 6-cycles is Berge-C₄-free
-- statement:
--   Let $G$ be a $C_8$-free bipartite graph with classes $A$ and $B$, and let $\mathcal H$ be the hypergraph on $B$ whose edge set is
--   $$\{N(v_1,v_3) : \{v_1,v_3\}\subseteq A \text{ is a fat pair contained in at least one fat } C_6\}.$$
--   Then $\mathcal H$ is Berge-$C_4$-free.
--
--   Together with Corollary 7 this gives (4): the sum of $|N(v_1,v_3)|$ over such fat pairs is $O(n^{1.5})$.
--
--   **Formalization Note** Equal neighbourhoods of different fat pairs give a single hyperedge, as in a set.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, pp. 15–16, §4.2, definition of 𝓗 and Claim 7

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_7 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : IsBipartition G A B) (hC8 : EvenCycleTuran.C4Count.CycleFree {8} G) :
    BergeC4Free (fatHypergraph G A) := by sorry

end EvenCycleTuran.BipC6C8
