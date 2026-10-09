-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_nonfat_c4_le
-- name    : EvenCycleTuran.C4Count.nonfat_c4_le
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:24:31.624754+00:00
-- url     : https://prove2.me/theorems/5e200031-a562-43e3-a686-76db43098641
-- title:
--   Proof of Theorem 11, p. 12 — at most C(k−1,2)·C(n,2) non-fat C₄'s
-- statement:
--   Let $k\ge 2$ and let $G$ be a $C_{2k}$-free graph on $n$ vertices. Call a pair of distinct vertices **fat** if they have at least $k$ common neighbours, and a copy of $C_4$ in $G$ **fat** if both of its pairs of opposite vertices are fat. Then the number of copies of $C_4$ in $G$ that are not fat is at most
--
--   $$\binom{k-1}{2}\binom{n}{2}.$$
--
--   Indeed there are at most $\binom n2$ non-fat pairs, and each lies as an opposite pair in at most $\binom{k-1}{2}$ copies of $C_4$. This is the first half of the upper bound in Theorem 11: it accounts for the main term $\frac{(k-1)(k-2)}4n^2$.
--
--   **Formalization Note** The freeness hypothesis follows the standing graph in the paper's proof. The opposite pairs of a copy are its pairs of distinct non-adjacent vertices.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 12, §4.1, proof of Theorem 11, second paragraph

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- §4.1, p. 12: the number of non-fat C₄'s of a C₂ₖ-free graph on `n` vertices is at most
C(k−1,2)·C(n,2). -/
theorem nonfat_c4_le {V : Type*} [Fintype V] [DecidableEq V] (G : SimpleGraph V)
    [DecidableRel G.Adj] (k : ℕ) (hk : 2 ≤ k) (hG : (cycleGraph (2 * k)).Free G) :
    nonFatC4Count G k ≤ (k - 1).choose 2 * (Fintype.card V).choose 2 := by sorry

end EvenCycleTuran.C4Count
