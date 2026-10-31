-- Prove2me | Theorems.Thm_FBMSP_oracle_operation_bound
-- name    : FBMSP.oracle_operation_bound
-- status  : Proved
-- author  : @mikeh
-- created : 2026-10-30T04:58:14.839261+00:00
-- url     : https://prove2.me/theorems/eb8778a5-9873-450f-8424-8606dd192f44
-- title:
--   Theorem 2, oracle step — Charged precomputation and reconstruction
-- statement:
--   Suppose each nonempty index interval $[a,b)$ with $b\le n$ has a declared oracle charge at most $m$. For $n,k\ge1$, summing these charges once over all nonempty intervals costs at most $m n(n+1)/2$. Adding the declared Bellman candidate evaluations for $k-1$ additional layers and $k$ backtracking steps gives
--   $$T(n,k,m)\le5n^2(k+m).$$
--   The primitive oracle's charge includes both the optimal price and attained block revenue.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Proof of Theorem 2, pp.43–44 (ec9–ec10).

import Definitions.Def_FBMSP_DynamicProgram

namespace FBMSP

theorem oracle_operation_bound (n k m : ℕ) (hn : 1 ≤ n) (hk : 1 ≤ k)
    (charge : ℕ → ℕ → ℕ)
    (hCost : ∀ a b, a < b → b ≤ n → charge a b ≤ m) :
    oracleCharges charge n ≤ m * blockOracleCalls n ∧
      segmentationWork charge k n ≤ 5 * (n * n) * (k + m) := by sorry

end FBMSP
