-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_proposition_10_gaps
-- name    : DERAggregation.MarketPower.proposition_10_gaps
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:00.942206+00:00
-- url     : https://prove2.me/theorems/283c7e3e-3362-429d-a441-ff69a03bd76c
-- title:
--   Proposition 10, p. 35 — the explicit welfare gaps (96a), (96c), (96d)
-- statement:
--   Consider the single-node market of §5 under Assumption 5, with $z^T_i=-C_i+(\alpha-b_i)/(2a_i)$. Then
--   $$\mathcal W^T-\mathcal W^{TN}=-\sum_{\{i\,:\,z^T_i\le0\}}a_i(z^T_i)^2; \tag{96a}$$
--   at every strategic outcome with participation,
--   $$\mathcal W^T-\mathcal W^S=\Big(\frac{\sum_iz^T_i}{N+1}\Big)^2\cdot\frac{1}{\sum_i\frac{1}{-a_i}}; \tag{96c}$$
--   and at every strategic outcome without participation, with purchases $d^{SN}$,
--   $$\mathcal W^{TN}-\mathcal W^{SN}=\sum_{\{i\,:\,d^{SN}_i=0,\ z^T_i>0\}}(-a_i)(z^T_i)^2+\Big(\frac{\sum_{\{i\,:\,d^{SN}_i>0\}}z^T_i}{N+1}\Big)^2\cdot\frac{1}{\sum_{\{i\,:\,d^{SN}_i>0\}}\frac{1}{-a_i}}. \tag{96d}$$
--
--   Each right-hand side is visibly nonnegative, which gives (46a), (46c) and (46d) of Theorem 3.
--
--   **Formalization Note** The printed (96d) writes $z_i^2$ in its first sum; the quantity meant is $(z^T_i)^2$, and that is formalized. The identity (96b) is (89) minus (91) and is not posed separately; the inequalities of Proposition 10 are those of Theorem 3. Assumption 5 includes the readings H1, H2 of its informal clauses; the bid layer is not modelled.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), §5.3, p. 35, Proposition 10, (96a), (96c), (96d)

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- Proposition 10 (p. 35), the explicit gaps (96a), (96c), (96d). Under Assumption 5, with
`z^T_i = −C_i + (α − b_i)/(2a_i)`:
(96a) `W^T − W^{TN} = −Σ_{i : z^T_i ≤ 0} a_i (z^T_i)²`;
(96c) `W^T − W^S = (Σ_i z^T_i / (N + 1))² · 1/(Σ_i 1/(−a_i))` at every strategic outcome with
participation;
(96d) `W^{TN} − W^{SN} = Σ_{i : d^{SN}_i = 0, z^T_i > 0} (−a_i)(z^T_i)² +
(Σ_{i : d^{SN}_i > 0} z^T_i / (N + 1))² · 1/(Σ_{i : d^{SN}_i > 0} 1/(−a_i))` at every strategic
outcome without participation (the printed `z_i²` in (96d) is `(z^T_i)²`). -/
theorem proposition_10_gaps {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) :
    WT a b C α N - WTN a b C α N =
      -(∑ i ∈ univ.filter (fun i => zT a b C α i ≤ 0), a i * zT a b C α i ^ 2) ∧
    (∀ (q lam : ℝ) (z : ι → ℝ), IsStratP a b C α N q lam z →
      WT a b C α N - welS a b C α N z q =
        ((∑ i, zT a b C α i) / ((N : ℝ) + 1)) ^ 2 * (1 / (∑ i, 1 / (-a i)))) ∧
    (∀ (q lam : ℝ) (d : ι → ℝ), IsStratN a b C α N q lam d →
      WTN a b C α N - welSN a b C α N d q =
        (∑ i ∈ univ.filter (fun i => d i = 0 ∧ 0 < zT a b C α i), (-a i) * zT a b C α i ^ 2) +
          ((∑ i ∈ univ.filter (fun i => 0 < d i), zT a b C α i) / ((N : ℝ) + 1)) ^ 2 *
            (1 / (∑ i ∈ univ.filter (fun i => 0 < d i), 1 / (-a i)))) := by sorry

end DERAggregation.MarketPower
