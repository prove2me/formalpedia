-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_10
-- name    : EvenCycleTuran.BipC6C8.claim_10
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:17.149722+00:00
-- url     : https://prove2.me/theorems/3f0f53a9-bf32-460b-b2e9-ccd71fc2098c
-- title:
--   Claim 10, p. 17 — the marked pairs not in a nice set number O(|A|^{1.5})
-- statement:
--   There is an absolute constant $C$ such that for every $C_8$-free bipartite graph $G$ with classes $A$ and $B$, the number of marked pairs $\{x,y\}\subseteq A$ (exactly three common neighbours) that are not contained in any nice set is at most
--   $$C\,|A|^{3/2}.$$
--
--   **Formalization Note** Pairs are unordered ($2$-subsets of $A$). The constant is chosen before the graph.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 17, §4.2, Claim 10

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_10 :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)),
      IsBipartition G A B → EvenCycleTuran.C4Count.CycleFree {8} G →
        (Nat.card {p : Finset (Fin n) //
            p ⊆ A ∧ IsMarked G p ∧ ¬ ∃ S, IsNice G A B S ∧ p ⊆ S} : ℝ) ≤
          C * (A.card : ℝ) ^ ((3 : ℝ) / 2) := by sorry

end EvenCycleTuran.BipC6C8
