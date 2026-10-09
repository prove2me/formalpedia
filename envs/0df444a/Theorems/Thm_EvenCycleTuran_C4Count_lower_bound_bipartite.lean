-- Prove2me | Theorems.Thm_EvenCycleTuran_C4Count_lower_bound_bipartite
-- name    : EvenCycleTuran.C4Count.lower_bound_bipartite
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-08T20:23:09.571123+00:00
-- url     : https://prove2.me/theorems/3bc450d6-f6c9-4533-9881-6a49d99b516a
-- title:
--   Proof of Theorem 11, p. 12 — K_{k−1,n−k+1} is C₂ₖ-free with C(k−1,2)·C(n−k+1,2) four-cycles
-- statement:
--   Let $k\ge 2$ and $n\ge k-1$. The complete bipartite graph $K_{k-1,n-k+1}$ contains no cycle of length $2k$, and the number of copies of $C_4$ in it is
--
--   $$\mathcal N(C_4,K_{k-1,n-k+1})=\binom{k-1}{2}\binom{n-k+1}{2}.$$
--
--   This is the lower-bound construction of Theorem 11: since $\binom{k-1}{2}\binom{n-k+1}{2}=(1+o(1))\frac{(k-1)(k-2)}{4}n^2$, it shows that the constant in Theorem 11 cannot be lowered.
--
--   **Formalization Note** $K_{k-1,n-k+1}$ is `bipGraph n (k - 1)` on `Fin n`. Copies are unlabelled (`copyCount`). The subtraction $n-(k-1)$ is in $\mathbb N$ and is exact under $n\ge k-1$.
-- source:
--   Gerbner, Győri, Methuku and Vizer, Generalized Turán problems for even cycles, arXiv:1712.07079v3, p. 12, §4.1, proof of Theorem 11, first sentence

import Mathlib
import Definitions.Def_EvenCycleTuran_C4Count_Setting
open Finset SimpleGraph Filter Topology

namespace EvenCycleTuran.C4Count

/-- §4.1, p. 12: `K_{k−1,n−k+1}` is C₂ₖ-free and contains C(k−1,2)·C(n−k+1,2) copies of C₄. -/
theorem lower_bound_bipartite (k n : ℕ) (hk : 2 ≤ k) (hn : k - 1 ≤ n) :
    CycleFree {2 * k} (bipGraph n (k - 1)) ∧
      (bipGraph n (k - 1)).copyCount (cycleGraph 4) =
        (k - 1).choose 2 * (n - (k - 1)).choose 2 := by sorry

end EvenCycleTuran.C4Count
