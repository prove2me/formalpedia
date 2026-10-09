-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_11
-- name    : EvenCycleTuran.BipC6C8.claim_11
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:25:48.436721+00:00
-- url     : https://prove2.me/theorems/13f9cfa7-5713-4705-a10b-0d4ccc9d36c9
-- title:
--   Claim 11, p. 18 — O(|A|²) bad triples contain neither a fat nor a marked pair
-- statement:
--   There is an absolute constant $C$ such that for every $C_8$-free bipartite graph $G$ with classes $A$ and $B$, the number of $3$-sets $\{x,y,z\}\subseteq A$ that are bad ($h(x,y,z)>6$) and contain neither a fat pair nor a marked pair is at most
--   $$C\,|A|^2.$$
--
--   **Formalization Note** $h(x,y,z)$ counts unlabelled $6$-cycles containing $x,y,z$. The constant is chosen before the graph.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 18, §4.2, Claim 11

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_11 :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)),
      IsBipartition G A B → EvenCycleTuran.C4Count.CycleFree {8} G →
        (Nat.card {T : Finset (Fin n) // T ⊆ A ∧ T.card = 3 ∧ 6 < hexCount G T ∧
            ∀ p ⊆ T, p.card = 2 → ¬ IsFatPair G p ∧ ¬ IsMarked G p} : ℝ) ≤
          C * (A.card : ℝ) ^ 2 := by sorry

end EvenCycleTuran.BipC6C8
