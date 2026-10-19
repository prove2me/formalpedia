-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_eq_93_95
-- name    : DERAggregation.MarketPower.eq_93_95
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:05.952684+00:00
-- url     : https://prove2.me/theorems/0283af12-3926-4cff-9a97-422a44e0b7b5
-- title:
--   (93) and (95), pp. 34–35 — the price rises δ and δ^N caused by strategic bidding
-- statement:
--   Consider the single-node market of §5 under Assumption 5, with $z^T_i=-C_i+(\alpha-b_i)/(2a_i)$ and $\lambda^T=\lambda^{TN}=\alpha$.
--
--   1. At every strategic outcome with participation, with price $\lambda^S$ and net purchases $z^S$, the price rise $\delta=\lambda^S-\alpha$ satisfies
--   $$\delta=\frac{\sum_i(z^S_i-z^T_i)}{\sum_i\frac{1}{2a_i}}=\frac{-\big(\frac{1}{N+1}\big)\sum_iz^T_i}{\sum_i\frac{1}{2a_i}}. \tag{93}$$
--   2. At every strategic outcome without participation, with price $\lambda^{SN}$ and purchases $d^{SN}$, at least one prosumer purchases a positive amount, and the price rise $\delta^N=\lambda^{SN}-\alpha$ satisfies
--   $$\delta^N=\frac{\sum_{\{i\,:\,d^{SN}_i>0\}}(-d^{SN}_i+z^T_i)}{-\sum_{\{i\,:\,d^{SN}_i>0\}}\frac{1}{2a_i}}=\frac{\frac{1}{N+1}\sum_{\{i\,:\,d^{SN}_i>0\}}z^T_i}{-\sum_{\{i\,:\,d^{SN}_i>0\}}\frac{1}{2a_i}}. \tag{95}$$
--
--   **Formalization Note** The nonemptiness of $\{i:d^{SN}_i>0\}$ is stated explicitly so that the denominator of (95) is a genuine nonzero sum. Assumption 5 includes the readings H1, H2 of its informal clauses; the bid layer is not modelled.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), §5.3, pp. 34–35, (92)–(95)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- (93) and (95), §5.3, pp. 34–35. Under Assumption 5, with `z^T_i = −C_i + (α − b_i)/(2a_i)`
and `λ^T = λ^{TN} = α`: at every strategic outcome with participation the price rise
`δ = λ^S − α` equals `Σ_i (z^S_i − z^T_i) / Σ_i 1/(2a_i) = −(1/(N+1)) Σ_i z^T_i / Σ_i 1/(2a_i)`
(93); at every strategic outcome without participation the set `{i : d^{SN}_i > 0}` is nonempty
and `δ^N = λ^{SN} − α` equals
`Σ_{d^{SN}_i > 0} (−d^{SN}_i + z^T_i) / (−Σ_{d^{SN}_i > 0} 1/(2a_i)) =
(1/(N+1)) Σ_{d^{SN}_i > 0} z^T_i / (−Σ_{d^{SN}_i > 0} 1/(2a_i))` (95). -/
theorem eq_93_95 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) :
    (∀ (q lam : ℝ) (z : ι → ℝ), IsStratP a b C α N q lam z →
      lam - α = (∑ i, (z i - zT a b C α i)) / (∑ i, 1 / (2 * a i)) ∧
      lam - α = -(1 / ((N : ℝ) + 1)) * (∑ i, zT a b C α i) / (∑ i, 1 / (2 * a i))) ∧
    (∀ (q lam : ℝ) (d : ι → ℝ), IsStratN a b C α N q lam d →
      (univ.filter (fun i => 0 < d i)).Nonempty ∧
      lam - α = (∑ i ∈ univ.filter (fun i => 0 < d i), (-d i + zT a b C α i)) /
        (-(∑ i ∈ univ.filter (fun i => 0 < d i), 1 / (2 * a i))) ∧
      lam - α = (1 / ((N : ℝ) + 1)) * (∑ i ∈ univ.filter (fun i => 0 < d i), zT a b C α i) /
        (-(∑ i ∈ univ.filter (fun i => 0 < d i), 1 / (2 * a i)))) := by sorry

end DERAggregation.MarketPower
