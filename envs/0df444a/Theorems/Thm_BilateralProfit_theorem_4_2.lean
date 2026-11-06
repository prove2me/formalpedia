-- Prove2me | Theorems.Thm_BilateralProfit_theorem_4_2
-- name    : BilateralProfit.theorem_4_2
-- status  : Open
-- author  : @iris
-- created : 2026-11-06T02:20:45.821446+00:00
-- url     : https://prove2.me/theorems/df50ecaf-e8ff-4871-b0f6-e4a094f4c5aa
-- title:
--   Theorem 4.2 — information inequality $\min_a\{\Delta_\rho(a)-\beta\mathcal I_\rho(a)\}\le C_0/K$
-- statement:
--   There is a universal constant $C_0$ such that, for every $K$ and every distribution $\rho$ over $G_K\times\mathcal A$, with $\beta=K^2\log^6K$,
--   $$\min_{a\in\mathcal A}\big\{\Delta_\rho(a)-\beta\cdot\mathcal I_\rho(a)\big\}\le\frac{C_0}K .$$
--
--   Against every table $\rho$, some price either has small expected gap or reveals much information about the coupling between the valuation and the action. This is the engine of Lemma 4.6 and hence of the regret bound.
--
--   **Formalization Note** $C_0$ is chosen before $K$ and $\rho$. The minimum over the finite nonempty $\mathcal A$ is written as the existence of a minimizing action. Logarithms are natural.
--
--   Differences from the source:
--   - encoding: the grid $G_K$ of step size $1/K$ → hypothesis $0<K$; reason: the step size $1/K$ presupposes $K\ge1$ (Lemma A.6: "for every integer $K\ge1$")
--   - encoding: $\min_{a\in\mathcal A}\{\cdot\}\le C_0/K$ → $\exists a\in\mathcal A$ with the value $\le C_0/K$; reason: equivalent over a finite nonempty set
-- source:
--   Brüstle, di Gregorio, Fusco, Leonardi, Regret Bounds for Profit Maximization in Bilateral Trade: Learning the Best Posted-Price Mechanism (manuscript, STOC 2027 submission, sha256 e91e81279505b765c7c96c219d674c0fbbbd6ca47a00da8fe228d498ca25ac87), Theorem 4.2, p.19 (PDF 21); proof pp.19–21 (PDF 21–23)

import Mathlib
import Definitions.Def_BilateralProfit_Analysis

namespace BilateralProfit

/-- **Theorem 4.2 (Information Inequality)**, Brüstle, di Gregorio, Fusco, Leonardi
(manuscript, sha256 e91e8127…), p.19 (PDF 21): there is a universal constant `C0` such that for
every distribution `ρ` over `G_K × 𝒜`, with `β = K² log⁶ K`,
`min_{a ∈ 𝒜} {Δ_ρ(a) − β ℐ_ρ(a)} ≤ C0/K`.

**Formalization Note.** `C0` is chosen before `K` and `ρ`. The minimum over the finite nonempty
`𝒜` is written as the existence of a minimizing action. `0 < K` is the grid's step size `1/K`. -/
theorem theorem_4_2 :
    ∃ C₀ : ℝ, ∀ K : ℕ, 0 < K → ∀ ρ : Grid K × Act K → ℝ, IsDist ρ →
      ∃ a : Act K, gap ρ a - beta K * info ρ a ≤ C₀ / K := by sorry

end BilateralProfit
