-- Prove2me | Theorems.Thm_BilateralOptRegret_lemma_2_1
-- name    : BilateralOptRegret.lemma_2_1
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T05:40:28.713636+00:00
-- url     : https://prove2.me/theorems/68ddbd28-25f3-4e7b-a132-7ec6c391b28e
-- title:
--   Lemma 2.1 — discretization error $2/(K-1)$
-- statement:
--   Let $L$ be a law on $[0,1]^2$ and $K\ge2$. The best grid profit approximates the best profit in $[0,1]^2$:
--   $$0\le\sup_{x\in[0,1]^2}r(x)-\mathrm{OPT}\le\frac{2}{K-1}.$$
--   Consequently any algorithm selecting actions from $\mathcal X_K$ satisfies
--   $$R_T\le\mathbb E\Big[\sum_{t=1}^T\mathrm{gap}(x_t)\Big]+\frac{2T}{K-1}.$$
--   This reduces the regret to the cumulative gap on the grid. It holds despite the profit not being Lipschitz.
--
--   Differences from the source:
--   - encoding: any algorithm selecting actions from $X_K$ → a deterministic policy on trade bits with values in grid points; reason: a randomized algorithm is a mixture of such policies, and the inequality is linear in the mixture
--   - encoding: $\mathrm{gap}(x_t)$ → $\mathrm{OPT}-r(x_t)$ at the point $x_t$; reason: $x_t$ is a grid point, where the two coincide
-- source:
--   Castiglioni, Lunghi, Marchesi, Optimal Regret for Profit Maximization in Bilateral Trade (manuscript, sha256 aafed174…), Lemma 2.1, p.14 (proof App. A, p.43)

import Mathlib
import Definitions.Def_BilateralProfit_Model
import Definitions.Def_BilateralProfit_QueryRoutine
import Definitions.Def_BilateralOptRegret_Model
import Definitions.Def_BilateralOptRegret_Regret

namespace BilateralOptRegret

open BilateralProfit MeasureTheory

/-- **Lemma 2.1**, Castiglioni, Lunghi, Marchesi, *Optimal Regret for Profit Maximization in Bilateral Trade* (manuscript, sha256 aafed174…), p.14; proof App. A, p.43: discretization.

For every `K ≥ 2`, `0 ≤ sup_{x ∈ [0,1]²} r(x) − OPT ≤ 2/(K − 1)`, and any algorithm selecting actions from `X_K`
satisfies `R_T ≤ E[∑_{t=1}^T gap(x_t)] + 2T/(K − 1)`.

**Formalization Note.** `K` is general here, as in the lemma. An algorithm selecting actions from `X_K` is a policy
all of whose values are grid points; for `x_t = x_q` the integrand `OPT − r(x_t)` is `gap(q)`. -/
theorem lemma_2_1 (K : ℕ) (hK : 2 ≤ K) (L : Measure (ℝ × ℝ)) (hL : IsValLaw L) :
    0 ≤ benchmark L - opt L K ∧ benchmark L - opt L K ≤ 2 / ((K : ℝ) - 1) ∧
    ∀ (Ω : Type) [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (X : ℕ → Ω → ℝ × ℝ) (π : List Bool → ℝ × ℝ) (T : ℕ),
      IsIIDRun P X L → (∀ h, ∃ q : Grid K, π h = pt K q) →
      regret P X L π T ≤
        (∫ ω, ∑ t ∈ Finset.range T, (opt L K - r L (act π X ω t)) ∂P) +
          2 * (T : ℝ) / ((K : ℝ) - 1) := by sorry

end BilateralOptRegret
