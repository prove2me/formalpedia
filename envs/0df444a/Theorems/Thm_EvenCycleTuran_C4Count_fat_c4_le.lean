-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_fat_c4_le
-- name    : EvenCycleTuran.C4Count.fat_c4_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:29.707336+00:00
-- url     : https://prove2.me/theorems/2867c904-0aa7-46bf-bcca-78a23c3641e8
-- title:
--   Proof of Theorem 11, pp. 12–13 — a C₂ₖ-free graph has at most 2(k−2)k²·C(2k,k)·|E(G)| fat C₄'s
-- statement:
--   Let $k\ge 2$ and let $G$ be a graph containing no cycle of length $2k$. Call a pair of distinct vertices fat if it has at least $k$ common neighbours, and a copy of $C_4$ fat if both of its opposite pairs are fat. Then the number of fat $C_4$'s in $G$ is at most
--
--   $$2(k-2)k^2\binom{2k}{k}\,|E(G)|.$$
--
--   Together with Theorem 1 this shows that the fat $C_4$'s number $O(n^{1+1/k})=o(n^2)$, so they do not contribute to the main term of Theorem 11.
--
--   **Formalization Note** The paper concludes "$O(n^{1+1/k})$"; the statement records the explicit bound its proof establishes, before Theorem 1 is applied. At $k=2$ the bound is $0$, which is correct: a fat $C_4$ is in particular a $C_4$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, pp. 12–13, §4.1, proof of Theorem 11 (third paragraph and conclusion via Claim 2)

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- §4.1, pp. 12–13: in a C₂ₖ-free graph the number of fat C₄'s is at most
2(k−2)k²·C(2k,k)·|E(G)|. -/
theorem fat_c4_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 2 ≤ k) (hG : (cycleGraph (2 * k)).Free G) :
    fatC4Count G k ≤ 2 * (k - 2) * k ^ 2 * (2 * k).choose k * #G.edgeFinset := by sorry

end EvenCycleTuran.C4Count
