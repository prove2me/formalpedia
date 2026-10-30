-- Prove2me | Theorems.Thm_FBMSP_theorem2_computing_segmentation
-- name    : FBMSP.theorem2_computing_segmentation
-- status  : Open
-- author  : @mikeh
-- created : 2026-10-30T04:58:41.100526+00:00
-- url     : https://prove2.me/theorems/b4166c70-7353-4176-8a6e-4dfdde85a22b
-- title:
--   Theorem 2 — Optimal segmentation and oracle computation
-- statement:
--   Let $n\ge1$ predicted values $\mu_1<\cdots<\mu_n$ be nonnegative, with positive weights summing to one. Let the independent common error have a finite first moment, mean zero, and MHR. For each index block $[a,b)$, an oracle supplies a nonnegative price attaining the block's maximum revenue. Its declared charge includes both the price and attained revenue, and is bounded by $m\ge1$ on every nonempty block.
--
--   For every $k\ge1$, there exist ordered cuts covering all $n$ types and a monotone assignment realizing those cuts, such that the oracle prices yield exactly the Bellman value and dominate every assignment to $k$ arbitrary nonnegative real prices. The specified bottom-up schedule, including precomputation and backtracking, satisfies
--   $$T(n,k,m)\le5n^2(k+m).$$
--
--   **Formalization note.** Empty blocks represent unused price slots. The last endpoint is $n$, so no type is omitted. This is an explicit oracle-operation cost model for sorted inputs, not a claim about the naive recursive evaluation or bit complexity of a continuous price oracle. The source's intended price-and-value oracle contract is made explicit.
-- source:
--   Titing Cui and Michael L. Hamilton, Optimal Feature-Based Market Segmentation and Pricing, October 22, 2025 manuscript (60 PDF pages); Operations Research 74(3), 1354–1370 (2026). https://doi.org/10.1287/opre.2022.0490 ; https://ssrn.com/abstract=4151103 . Theorem 2, p.17; proof pp.43–44 (ec9–ec10), Eq. (EC.6).

import Definitions.Def_FBMSP_Model
import Definitions.Def_FBMSP_DynamicProgram

namespace FBMSP

theorem theorem2_computing_segmentation
    {n k : ℕ} (hk : 1 ≤ k) (η : MeasureTheory.Measure ℝ)
    (hη : ValidNoise η) (hMHR : HasMHR η)
    (μ w : Fin n → ℝ) (hMarket : ValidFiniteMarket μ w)
    (o : ℕ → ℕ → ℝ) (ho : BlockOracle η μ w o)
    (charge : ℕ → ℕ → ℕ) (m : ℕ) (hm : 1 ≤ m)
    (hCost : ∀ a b, a < b → b ≤ n → charge a b ≤ m) :
    ∃ (c : Fin (k + 1) → ℕ) (a : Fin n → Fin k),
      ValidCuts n k c ∧ RealizesCuts a c ∧ Monotone a ∧
      finitePolicyRevenue η μ w a
        (fun j => o (c j.castSucc) (c j.succ)) =
          intervalDP (oracleScore η μ w o) (k - 1) 0 n ∧
      (∀ (a' : Fin n → Fin k) (p' : Fin k → ℝ),
        (∀ j, 0 ≤ p' j) →
        finitePolicyRevenue η μ w a' p' ≤
          finitePolicyRevenue η μ w a
            (fun j => o (c j.castSucc) (c j.succ))) ∧
      segmentationWork charge k n ≤ 5 * (n * n) * (k + m) := by sorry

end FBMSP
