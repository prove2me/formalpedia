-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_proposition_5
-- name    : DERAggregation.MarketPower.proposition_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:13.109289+00:00
-- url     : https://prove2.me/theorems/4549de7e-84a8-432e-b2ff-d4f412360249
-- title:
--   Proposition 5, p. 28 — truthful generators with participation: the optimum (50), price λ^T = α, and W^T = αC − Σ(b_i − α)²/(4a_i)
-- statement:
--   Consider the single-node market of §5 with prosumer participation and truthful generators, under Assumption 5. Let
--   $$z^T_i=-C_i+\frac{\alpha-b_i}{2a_i},\qquad y^T_j=\frac{-C+\sum_i\frac{\alpha-b_i}{2a_i}}{N}\quad(j=1,\dots,N). \tag{50}$$
--   Then:
--   1. $(z^T,y^T)$ is feasible for the dispatch problem (49) and attains its maximum welfare;
--   2. at the price $\lambda^T=\alpha$, each $z^T_i$ is prosumer $i$'s optimal response and $\sum_iz^T_i=Ny^T_j$, so $\alpha$ clears the market at the optimal supply;
--   3. the optimal welfare is
--   $$\mathcal W^T=\alpha C-\sum_i\frac{(b_i-\alpha)^2}{4a_i}. \tag{51}$$
--
--   This is the efficient benchmark against which the strategic outcome with participation is measured.
--
--   **Formalization Note** The paper's "equilibrium market price (the optimal Lagrange multiplier of the constraint) is $\lambda^T=\alpha$" is stated as item 2: at price $\alpha$ the price-taking prosumers' optimal responses are $z^T$ and clear the optimal supply; for this problem with one equality constraint and interior responses, that is the multiplier property. Assumption 5 includes the precise readings H1, H2 of its informal clauses (see the Setting). $\mathcal W^T$ is defined as a supremum, so item 3 is meaningful only together with item 1, which shows the supremum is attained.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 28, Proposition 5, (50)–(51)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- Proposition 5 (p. 28). Under Assumption 5, `z^T_i = −C_i + (α − b_i)/(2a_i)` and
`y^T_j = (−C + Σ_i (α − b_i)/(2a_i))/N` (50) form an optimal solution of (49); at the price
`λ^T = α` every prosumer's optimal response is `z^T_i` and the market clears at the total supply
`N y^T_j`; and the optimal welfare is `W^T = αC − Σ_i (b_i − α)²/(4a_i)` (51). -/
theorem proposition_5 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) :
    let yT : ℝ := (-(∑ i, C i) + (∑ i, (α - b i) / (2 * a i))) / (N : ℝ)
    FeasT C N (zT a b C α) (fun _ => yT) ∧
    (∀ (z : ι → ℝ) (y : Fin N → ℝ), FeasT C N z y →
      welT a b C α N z y ≤ welT a b C α N (zT a b C α) (fun _ => yT)) ∧
    ClearsP a b C ((N : ℝ) * yT) α (zT a b C α) ∧
    WT a b C α N = α * (∑ i, C i) - (∑ i, (b i - α) ^ 2 / (4 * a i)) := by sorry

end DERAggregation.MarketPower
