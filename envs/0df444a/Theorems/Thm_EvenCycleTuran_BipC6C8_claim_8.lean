-- Prove2me | Theorems.Thm_EvenCycleTuran_BipC6C8_claim_8
-- name    : EvenCycleTuran.BipC6C8.claim_8
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T21:29:46.803366+00:00
-- url     : https://prove2.me/theorems/f60a065d-7e5a-40b9-9a7c-e99641649bd3
-- title:
--   Claim 8, p. 16 — a bipartite C₈-free graph on n vertices has O(n^{2.5}) fat 6-cycles
-- statement:
--   There is an absolute constant $C$ such that for every $n$ and every $C_8$-free bipartite graph $G$ on $n$ vertices (with any bipartition $(A,B)$), the number of fat $6$-cycles of $G$ is at most
--   $$C\,n^{5/2}.$$
--
--   The fat $6$-cycles are those with fat pairs in both classes; the remaining $6$-cycles are handled by Claims 9–11.
--
--   **Formalization Note** Fat $6$-cycles are counted labelled, as injective maps $\{0,\dots,5\}\to V$; each unlabelled cycle corresponds to $12$ of them, a factor absorbed in $C$. The constant is chosen before $n$ and $G$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 16, §4.2, Claim 8

import Mathlib
import Definitions.Def_EvenCycleTuran_BipC6C8_Setting
open Finset SimpleGraph Filter Asymptotics

namespace EvenCycleTuran.BipC6C8

theorem claim_8 :
    ∃ C : ℝ, ∀ (n : ℕ) (G : SimpleGraph (Fin n)) (A B : Finset (Fin n)),
      IsBipartition G A B → EvenCycleTuran.C4Count.CycleFree {8} G →
        (Nat.card {v : Fin 6 → Fin n // IsFatHexagon G v} : ℝ) ≤
          C * (n : ℝ) ^ ((5 : ℝ) / 2) := by sorry

end EvenCycleTuran.BipC6C8
