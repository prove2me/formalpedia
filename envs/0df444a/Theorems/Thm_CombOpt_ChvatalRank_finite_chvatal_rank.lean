-- Prove2me | Theorems.Thm_CombOpt_ChvatalRank_finite_chvatal_rank
-- name    : CombOpt.ChvatalRank.finite_chvatal_rank
-- status  : Open
-- author  : @iris
-- created : 2026-10-30T22:09:28.608448+00:00
-- url     : https://prove2.me/theorems/68203c7c-741b-4e9b-b8c7-74b691a3e944
-- title:
--   Theorem 6.35 — every rational polytope has finite Chvátal rank
-- statement:
--   Let $P$ be a rational polytope, and let $P^{(0)}=P$ and $P^{(i)}=(P^{(i-1)})'$ for all positive integers $i$. Then there is an integer $k\ge0$ with
--   $$
--   P^{(k)}=P_I.
--   $$
--   The least such $k$ is the **Chvátal rank** of $P$. The theorem says that the convex hull of the integral vectors of a rational polytope is reached by finitely many rounds of Gomory–Chvátal cuts.
--
--   **Formalization Note** $k$ is a natural number, and $k=0$ occurs exactly when $P=P_I$, for instance for $P=\emptyset$.
--
--   Differences from the source: none.
-- source:
--   Cook, Cunningham, Pulleyblank & Schrijver, Combinatorial Optimization (Wiley, 1998), Theorem 6.35, p. 234 (PDF 242)

import Mathlib
import Definitions.Def_CombOpt_ChvatalRank_IsRationalPolytope
import Definitions.Def_CombOpt_ChvatalRank_chvatalIter
import Definitions.Def_CombOpt_ChvatalRank_integerHull

open Matrix

namespace CombOpt.ChvatalRank

/-- **Theorem 6.35.** Cook, Cunningham, Pulleyblank & Schrijver, *Combinatorial Optimization* (Wiley, 1998), Theorem 6.35, p. 234 (PDF 242): "If P is a rational polytope, then P^(k) = P_I for
some integer k." (Chvátal 1973, Schrijver 1980.) The least such `k` is the Chvátal rank of `P`.

**Formalization Note.** `k : ℕ`; `k = 0` occurs when `P = P_I`, for instance for `P = ∅`. The whole of
`P^(k)` in `ℝⁿ` equals the real convex hull of the integral points of `P`. -/
theorem finite_chvatal_rank {n : ℕ} {P : Set (Fin n → ℝ)} (hP : IsRationalPolytope P) :
    ∃ k : ℕ, chvatalIter P k = integerHull P := by sorry

end CombOpt.ChvatalRank
