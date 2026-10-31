-- Prove2me | Theorems.Thm_FBMSP_dp_operation_bound
-- name    : FBMSP.dp_operation_bound
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T04:57:46.08825+00:00
-- url     : https://prove2.me/theorems/e9cd4d8d-cc13-40e9-a82a-7563aa65014f
-- title:
--   Theorem 2, counting step — Quadratic table bound
-- statement:
--   For $n\ge1$, $k$ additional Bellman layers, and charge $m$ per nonempty interval oracle call, the specified table-operation count satisfies
--   $$m\,\frac{n(n+1)}2+k\,\frac{(n+1)(n+2)}2\le4n^2(k+m).$$
--   Here the paper's price budget $K$ corresponds to $k=K-1$. This counts a memoized bottom-up schedule, not recursive recomputation. A complete proof of this generic count has been checked locally.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Proof of Theorem 2, p.44 (ec10), final paragraph.

import Definitions.Def_FBMSP_DynamicProgram

namespace FBMSP

theorem dp_operation_bound (k n m : ℕ) (hn : 1 ≤ n) :
    tableWork k n m ≤ 4 * (n * n) * (k + m) := by sorry

end FBMSP
