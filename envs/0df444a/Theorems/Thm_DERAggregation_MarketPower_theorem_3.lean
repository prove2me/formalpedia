-- Prove2me | Theorems.Thm_DERAggregation_MarketPower_theorem_3
-- name    : DERAggregation.MarketPower.theorem_3
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-16T11:25:04.559493+00:00
-- url     : https://prove2.me/theorems/eb5597b7-4df9-4697-9bef-225988223dd8
-- title:
--   Theorem 3, p. 27 — prosumer participation raises welfare and shrinks the welfare loss from strategic bidding, (46a)–(46e)
-- statement:
--   Consider the single-node market of §5 with prosumers $i$ (capacity $C_i$, utility $u_i(z)=a_iz^2+b_iz$) and $N$ identical generators with linear cost $\alpha y$, under Assumption 5. Let $\mathcal W^T$ and $\mathcal W^{TN}$ be the optimal social welfares of the dispatch problems with prosumer participation (49) and without it (69), and let $\mathcal W^S$ and $\mathcal W^{SN}$ be the true social welfares at a strategic outcome — a symmetric pure equilibrium of the generators' quantity game against the market-clearing price of price-taking prosumers — with and without participation. Then
--   $$\mathcal W^T\ge\mathcal W^{TN}, \tag{46a}$$
--   $$\mathcal W^S\ge\mathcal W^{SN}, \tag{46b}$$
--   $$\mathcal W^T\ge\mathcal W^S, \tag{46c}$$
--   $$\mathcal W^{TN}\ge\mathcal W^{SN}, \tag{46d}$$
--   $$\mathcal W^{TN}-\mathcal W^{SN}\ge\mathcal W^T-\mathcal W^S, \tag{46e}$$
--   where each inequality involving $\mathcal W^S$ or $\mathcal W^{SN}$ holds for every strategic outcome of the respective model.
--
--   Prosumer participation thus raises welfare whether generators bid truthfully or strategically, and the welfare lost to the generators' market power is smaller with participation than without it.
--
--   **Formalization Note** Assumption 5's informal clauses are read as H1 (the participation clearing price at zero generator supply lies below every $b_i$) and H2 ($-C+\sum_i(\alpha-b_i)/(2a_i)>0$); the paper's §5.4 example satisfies both. The paper's strategic generators bid tilted cost functions that implement the quantity equilibrium (Lemmas 5 and 8); that bid layer is not modelled, and $\mathcal W^S,\mathcal W^{SN}$ are the true welfares at the quantity equilibrium, as in the paper's proofs. The strategic outcome with participation exists and is unique; the paper does not show that one without participation exists, so (46b), (46d), (46e) are stated for every such outcome. $\mathcal W^T,\mathcal W^{TN}$ are suprema, attained by Propositions 5 and 7.
-- source:
--   Gao, Alshehri, Birge, Aggregating Distributed Energy Resources: Efficiency and Market Power, working paper, SSRN abstract 3931052 (PDF of September 26, 2021), p. 27, Theorem 3, (46a)–(46e); proof §5.3 and Proposition 10, pp. 34–35

import Mathlib
import Definitions.Def_DERAggregation_MarketPower_Setting

namespace DERAggregation.MarketPower

open Finset

/-- Theorem 3 (p. 27). Under Assumption 5:
(46a) `W^T ≥ W^{TN}`;
(46b) `W^S ≥ W^{SN}`;
(46c) `W^T ≥ W^S`;
(46d) `W^{TN} ≥ W^{SN}`;
(46e) `W^{TN} − W^{SN} ≥ W^T − W^S`,
where `W^T`, `W^{TN}` are the optimal welfares of (49), (69), and `W^S`, `W^{SN}` are the true
welfares at any strategic outcome (symmetric pure equilibrium of the generators' quantity game
(56), resp. (75)) with, resp. without, prosumer participation. -/
theorem theorem_3 {ι : Type*} [Fintype ι] (a b C : ι → ℝ) (α : ℝ) (N : ℕ)
    (h5 : Assumption5 a b C α N) :
    WTN a b C α N ≤ WT a b C α N ∧
    (∀ (q lam : ℝ) (z : ι → ℝ) (qN lamN : ℝ) (d : ι → ℝ),
      IsStratP a b C α N q lam z → IsStratN a b C α N qN lamN d →
        welSN a b C α N d qN ≤ welS a b C α N z q) ∧
    (∀ (q lam : ℝ) (z : ι → ℝ), IsStratP a b C α N q lam z →
      welS a b C α N z q ≤ WT a b C α N) ∧
    (∀ (qN lamN : ℝ) (d : ι → ℝ), IsStratN a b C α N qN lamN d →
      welSN a b C α N d qN ≤ WTN a b C α N) ∧
    (∀ (q lam : ℝ) (z : ι → ℝ) (qN lamN : ℝ) (d : ι → ℝ),
      IsStratP a b C α N q lam z → IsStratN a b C α N qN lamN d →
        WT a b C α N - welS a b C α N z q ≤ WTN a b C α N - welSN a b C α N d qN) := by sorry

end DERAggregation.MarketPower
