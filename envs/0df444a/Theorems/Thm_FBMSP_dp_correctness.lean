-- Prove2me | Theorems.Thm_FBMSP_dp_correctness
-- name    : FBMSP.dp_correctness
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T04:57:23.261548+00:00
-- url     : https://prove2.me/theorems/e7f7ea65-42dd-46d6-91a9-80c369a5c3ff
-- title:
--   Eq. (EC.6) — Bellman optimality for consecutive blocks
-- statement:
--   Let $W(a,b)$ be any real score assigned to the index interval $[a,b)$. The declared Bellman recurrence for $k+1$ consecutive block slots on $[a,a+n)$ is attained by a witnessed partition and is at least the score of every such partition.
--
--   Empty blocks are allowed. When their scores are zero, they represent unused slots. This is a generic combinatorial lemma; applying it to pricing requires the block-oracle and interval-reduction links. A complete proof of this generic lemma has been checked locally, but this uploaded draft target remains an open statement until publication and proof submission.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Proof of Theorem 2, pp.43–44 (ec9–ec10), Eq. (EC.6).

import Definitions.Def_FBMSP_DynamicProgram

namespace FBMSP

theorem dp_correctness (W : ℕ → ℕ → ℝ) (k a n : ℕ) :
    IntervalValue W k a n (intervalDP W k a n) ∧
      ∀ v, IntervalValue W k a n v → v ≤ intervalDP W k a n := by sorry

end FBMSP
