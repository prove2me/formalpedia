-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_one_side_count
-- name    : EvenCycleTuran.BipC6C8.one_side_count
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:37.738244+00:00
-- url     : https://prove2.me/theorems/9c597e8a-06d4-428b-b945-32f22e653515
-- title:
--   pp. 17–18 — 6-cycles with no fat pair in A number at most 6·C(|A|, 3) + O(|A|^{2.5})
-- statement:
--   There is an absolute constant $C$ such that for every $n$ and every $C_8$-free bipartite graph $G$ on $n$ vertices with classes $A$ and $B$, the number of $6$-cycles of $G$ containing no fat pair from $A$ is at most
--   $$6\binom{|A|}{3}+C\,|A|^{5/2}.$$
--
--   With the symmetric bound for $B$ and Claim 8 this gives $\mathrm{ex}_{bip}(n,C_6,C_8)\le 6\binom{|A|}{3}+6\binom{|B|}{3}+O(n^{5/2})\le n^3+O(n^{5/2})$.
--
--   **Formalization Note** $6$-cycles are unlabelled (subgraphs isomorphic to $C_6$). A cycle "contains a fat pair from $A$" if two of its vertices in $A$ form a fat pair. This is the final display of §4.2 (p. 18); the announcement on p. 17 speaks of the cycles with fat pairs "just from one side, say $B$", which are among those counted here. The constant is chosen before $n$ and $G$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 17, §4.2, paragraph after Claim 8; p. 18, final display of §4.2

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem one_side_count :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)),
      IsBipartition G A B → EvenCycleTuran.C4Count.CycleFree {8} G →
        (Nat.card {H : G.Subgraph // Nonempty (cycleGraph 6 ≃g H.coe) ∧
            ∀ p : Finset (Fin n), p ⊆ A → (p : Set (Fin n)) ⊆ H.verts → ¬ IsFatPair G p} : ℝ) ≤
          6 * ((A.card.choose 3 : ℕ) : ℝ) + C * (A.card : ℝ) ^ ((5 : ℝ) / 2) := by sorry

end EvenCycleTuran.BipC6C8
