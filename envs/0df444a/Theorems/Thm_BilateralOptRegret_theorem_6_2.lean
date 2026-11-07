-- Prove2me | Theorems.Thm_BilateralOptRegret_theorem_6_2
-- name    : BilateralOptRegret.theorem_6_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:42:47.911541+00:00
-- url     : https://prove2.me/theorems/dd868d43-9263-401e-b092-e8bfd05875ba
-- title:
--   Theorem 6.2 — sampling fixed-endpoint blocks
-- statement:
--   There is an absolute constant $C_0>0$ with the following property. Let $v_j$ be arbitrary maps, $G_{\mathrm{qry}}$ an arbitrary set, $\beta\in(0,1]$, $\delta\in(0,1)$ and $\delta_0\in(0,1)$ with (number of BinS calls)$\cdot\delta_0\le\delta$. Then $|\mathcal P|\le|\mathcal I^\star|+K+C\le3K+C$. Running Algorithm 4 with precision $\beta$ and failure probability $\delta_0$ on each block with distinct endpoints and at least one eligible row gives, with probability at least $1-\delta$, estimates with error at most $\beta$ on all columns and all rows at which both endpoints are queryable, and on the same event the number of observations is at most
--   $$C_0\log\frac{4K}{\delta_0}\Big[(3K+C)\beta^{-2}+\lceil\log_2K\rceil V\beta^{-3}\Big].$$
--   The printed choice $\delta_0=\delta/(3K+C)$ gives the printed bound (14).
--
--   **Formalization Note** On coinciding endpoints the estimate is $0$, which is the true difference.
--
--   Differences from the source:
--   - generalization: $\delta_0=\delta/(3K+C)$, and $\log(4K(3K+C)/\delta)$ in (14) → any $\delta_0\in(0,1)$ with (number of calls)$\cdot\delta_0\le\delta$, and $\log(4K/\delta_0)$; reason: the printed $\delta_0$ is an instance, since the calls number at most $|\mathcal P|\le3K+C$; Algorithm 3 itself uses $\delta/(6K^2)$ (p.38)
--   - encoding: $O(\cdot)$ in (14) → $\exists C_0>0$ before all quantifiers; reason: the proof gives an absolute constant
--   - encoding: $K\ge 2$ with $K-1$ a power of two (standing, p.13) → $K=2^n+1$, indices `Fin (2^n+1)`, $\ell_K=n+1$; reason: the page assumes this throughout §§4–8; every such $K$ has this form
--   - encoding: a procedure → a deterministic adaptive program `QTree` over grid actions, with the query list from `traced`; reason: Algorithms 1, 3, 4 use no internal randomness, and a program cannot read the law; the clauses on one event are an event on (output, query list)
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Theorem 6.2, p.24, with $|\mathcal P|\le3K+C$, p.23

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Program
import Definitions.Def_BilateralOptRegret_Dyadic
import Definitions.Def_BilateralOptRegret_Blocks

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Theorem 6.2**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.24: sampling fixed-endpoint blocks.

For arbitrary mappings `v_j` and an arbitrary queryable set, `|P| ≤ |I⋆| + K + C ≤ 3K + C`. If BinS runs on each block with distinct endpoints and an
eligible row, with precision `β ∈ (0, 1]` and failure probability `δ₀`, where (number of calls)·`δ₀ ≤ δ`, then with probability at least `1 − δ` all estimates
have error at most `β`, on all columns and all rows where both endpoints are queryable, and on the same event the number of observations is
`O(log(4K/δ₀) [(3K + C) β⁻² + ⌈log₂ K⌉ V β⁻³])`, (14), with an absolute constant.

**Formalization Note.** The printed choice `δ₀ = δ/(3K + C)` is the special case: it has `δ₀ ∈ (0, 1)`, and the number of calls is at most `|P| ≤ 3K + C`,
and it turns `log(4K/δ₀)` into `log(4K(3K + C)/δ)`. The general `δ₀` is needed because Algorithm 3 calls BinS with `δ/(6K²)` (p.38). On coinciding endpoints the table
holds `0`, the true difference. -/
theorem theorem_6_2 :
    ∃ C₀ : ℝ, 0 < C₀ ∧ ∀ (n : ℕ) (v : ℕ → Idx n → Idx n) (Gqry : Finset (Act n)) (β δ δ₀ : ℝ),
      0 < β → β ≤ 1 → 0 < δ → δ < 1 → 0 < δ₀ → δ₀ < 1 →
      ((callBlocks v Gqry).card : ℝ) * δ₀ ≤ δ →
      ∀ L : Measure (ℝ × ℝ), IsValLaw L →
        (blocks v).card ≤ (Istar n).card + Kof n + changeCount v ∧
        (Istar n).card + Kof n + changeCount v ≤ 3 * Kof n + changeCount v ∧
        ENNReal.ofReal (1 - δ) ≤
          succProb L (Kof n) (runBlocks v Gqry β δ₀) (fun o =>
            (∀ c ∈ cols n, ∀ j : Idx n,
              ((colEnds v j.val c).1, j) ∈ Gqry → ((colEnds v j.val c).2, j) ∈ Gqry →
              |o.1 c j - rowDiff L (Kof n) j (colEnds v j.val c).2 (colEnds v j.val c).1| ≤ β) ∧
            (o.2.length : ℝ) ≤
              C₀ * Real.log (4 * (Kof n : ℝ) / δ₀) *
                ((3 * (Kof n : ℝ) + (changeCount v : ℝ)) * β ^ (-2 : ℤ) +
                  (Nat.clog 2 (Kof n) : ℝ) * massV L v Gqry * β ^ (-3 : ℤ))) := by sorry

end BilateralOptRegret
