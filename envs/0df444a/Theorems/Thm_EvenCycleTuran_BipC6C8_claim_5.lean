-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_5
-- name    : EvenCycleTuran.BipC6C8.claim_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:10.327127+00:00
-- url     : https://prove2.me/theorems/11b8dbe2-2cc3-4f0c-8e49-535ef046738a
-- title:
--   Claim 5, p. 14 — distinct fat pairs of fat 6-cycles in A have |N(v₁, v₃) ∩ N(v′₁, v′₃)| ≤ 1
-- statement:
--   Let $G$ be a $C_8$-free bipartite graph with classes $A$ and $B$. Let $\{v_1,v_3\}\ne\{v_1',v_3'\}$ be fat pairs contained in $A$, each lying on some fat $6$-cycle. Then
--   $$|N(v_1,v_3)\cap N(v_1',v_3')|\le 1.$$
--
--   So the common neighbourhoods of distinct fat pairs are almost disjoint; this is what makes the hypergraph $\mathcal H$ of Claim 7 well behaved.
--
--   **Formalization Note** "Fat pair of a fat $6$-cycle" is encoded as "fat pair whose two vertices lie on a fat $6$-cycle"; in a bipartite graph two same-class vertices of a $6$-cycle are at distance two on it, so this is the same thing.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 14, §4.2, Claim 5

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_5 {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    (A B : Finset V) (hAB : IsBipartition G A B) (hC8 : EvenCycleTuran.C4Count.CycleFree {8} G)
    (p q : Finset V) (hpA : p ⊆ A) (hqA : q ⊆ A) (hpq : p ≠ q)
    (hp : IsFatPair G p) (hq : IsFatPair G q) (hpC : InFatHexagon G p) (hqC : InFatHexagon G q) :
    (commonNbrs G p ∩ commonNbrs G q).card ≤ 1 := by sorry

end EvenCycleTuran.BipC6C8
