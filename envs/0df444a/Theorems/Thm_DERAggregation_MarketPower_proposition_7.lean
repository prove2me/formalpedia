-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_proposition_7
-- name    : DERAggregation.MarketPower.proposition_7
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:24:57.583995+00:00
-- url     : https://prove2.me/theorems/d83cac21-8a63-4248-8ea4-1d5f057a45c5
-- title:
--   Proposition 7, p. 31 — truthful generators without participation: the optimum (70), price λ^TN = α, and the welfare W^TN of (71)
-- statement:
--   Consider the single-node market of §5 without prosumer participation (prosumers can only buy, $d_i\ge0$) and with truthful generators, under Assumption 5. Let
--   $$d^{TN}_i=\Big[-C_i+\frac{\alpha-b_i}{2a_i}\Big]^+,\qquad y^{TN}_j=\frac{\sum_i d^{TN}_i}{N}\quad(j=1,\dots,N). \tag{70}$$
--   Then:
--   1. $(d^{TN},y^{TN})$ is feasible for the dispatch problem (69) and attains its maximum welfare;
--   2. at the price $\lambda^{TN}=\alpha$ each $d^{TN}_i$ is prosumer $i$'s optimal purchase and the market clears at the total $Ny^{TN}_j$;
--   3. the optimal welfare is
--   $$\mathcal W^{TN}=\sum_{\{i\,:\,2a_iC_i+b_i>\alpha\}}\Big[\alpha C_i-\frac{(b_i-\alpha)^2}{4a_i}\Big]+\sum_{\{i\,:\,2a_iC_i+b_i\le\alpha\}}\big(a_iC_i^2+b_iC_i\big). \tag{71}$$
--
--   **Formalization Note** The proposition as printed says "an optimal solution to (49)"; the problem meant is (69), and that is what is formalized. The price claim is stated, as in Proposition 5, as market clearing by price-taking prosumers at price $\alpha$. $\mathcal W^{TN}$ is a supremum; item 1 shows it is attained. Assumption 5 includes the readings H1, H2 of its informal clauses.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 31, Proposition 7, (69)–(71)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- Proposition 7 (p. 31; "(49)" there is a misprint for (69)). Under Assumption 5,
`d^{TN}_i = [−C_i + (α − b_i)/(2a_i)]^+` and `y^{TN}_j = Σ_i d^{TN}_i / N` (70) form an optimal
solution of (69); at the price `λ^{TN} = α` every prosumer's optimal purchase is `d^{TN}_i` and
the market clears at the total supply `N y^{TN}_j`; and the optimal welfare is (71). -/
theorem proposition_7 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) :
    let dTN : ι → ℝ := fun i => max (-C i + (α - b i) / (2 * a i)) 0
    let yTN : ℝ := (∑ i, dTN i) / (N : ℝ)
    FeasTN N dTN (fun _ => yTN) ∧
    (∀ (d : ι → ℝ) (y : Fin N → ℝ), FeasTN N d y →
      welT a b C α N d y ≤ welT a b C α N dTN (fun _ => yTN)) ∧
    ClearsN a b C ((N : ℝ) * yTN) α dTN ∧
    WTN a b C α N =
      (∑ i ∈ univ.filter (fun i => α < 2 * a i * C i + b i),
          (α * C i - (b i - α) ^ 2 / (4 * a i))) +
        (∑ i ∈ univ.filter (fun i => 2 * a i * C i + b i ≤ α), (a i * C i ^ 2 + b i * C i)) := by sorry

end DERAggregation.MarketPower
