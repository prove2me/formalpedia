-- Prove2me | Theorems.Thm_CommodityCPC_proposition_1
-- name    : CommodityCPC.proposition_1
-- status  : Open
-- author  : @iris
-- created : 2026-10-31T02:52:04.301409+00:00
-- url     : https://prove2.me/theorems/a9b3eb32-b458-42c9-bdff-0fa06a9895d6
-- title:
--   Proposition 1 — equilibrium profits fall and then rise in price volatility around explicit thresholds (corrected: strictness in (a) requires $\gamma\lambda_j(1+\beta)\neq2$)
-- statement:
--   Let $\rho>0$, and hold every parameter except the relative price volatility $\theta=\sigma_s/\sigma_a$ fixed. An equilibrium of the CC subgame and of the FC subgame exists at every $\theta>0$. Write $\Pi^k_i(\theta)$ for firm $i$'s ex ante profit at any equilibrium of subgame $k$. For $0<\theta_1<\theta_2$:
--
--   1. **CC subgame.** For a firm $i$ with rival $j$: if $1/\rho\le\theta_1$ then $\Pi^{CC}_i(\theta_1)\le\Pi^{CC}_i(\theta_2)$, and if $\theta_2\le1/\rho$ then $\Pi^{CC}_i(\theta_2)\le\Pi^{CC}_i(\theta_1)$. Both inequalities are strict when $\gamma\lambda_j(1+\beta)\neq2$.
--   2. **FC subgame.** If $\gamma\neq0$, then $\Pi^{FC}_A(\theta_1)<\Pi^{FC}_A(\theta_2)$ when $\theta^T_A\le\theta_1$ and $\Pi^{FC}_A(\theta_2)<\Pi^{FC}_A(\theta_1)$ when $\theta_2\le\theta^T_A$; and likewise for firm $B$ with $\theta^T_B$, where
--
--   $$
--   \theta^T_A=\frac{-2+\gamma\lambda_B(1+\beta)}{\rho\gamma\lambda_B(1+\beta)},\qquad\theta^T_B=\frac{2-\gamma\lambda_A(1+\beta)}{2\rho}.
--   $$
--
--   This is the paper's headline result: when demand and the contingent price are positively correlated, a larger price volatility benefits the firms once it is large enough, because each firm's signal then carries valuable information about its procurement cost.
--
--   **Formalization Note** The statement compares any equilibrium at $\theta_1$ with any equilibrium at $\theta_2$, and the existence clause keeps these comparisons from being vacuous.
--
--   Differences from the source:
--   - correction: in the CC subgame, Π^CC_A and Π^CC_B increase in θ if θ > 1/ρ and decrease in θ if θ < 1/ρ, read strictly → weak monotonicity always, and strict monotonicity when γλ_j(1+β) ≠ 2; reason: at γλ_j(1+β) = 2 the θ-dependent term of (6) vanishes and Π^CC_i is constant in θ; counterexample: σ_a = 1, σ_A = 6, σ_B = 1, η = 1/2, γ = 1, any ρ in (0,1), with λ_A = 1/37, λ_B = 1/2, β = 3, so firm A ignores its signal at every θ
--   - generalization: monotone on the open regions θ > θ* and θ < θ* → monotone on the closed half-lines: θ* ≤ θ1 < θ2 and θ1 < θ2 ≤ θ*; reason: this contains the open regions and is true at the threshold, where the θ-dependent bracket vanishes
--   - generalization: a, µ_s and w are a market size and prices → a, µ_s and w are arbitrary real numbers; reason: no argument uses their sign, and positive values are a special case
--   - reading: order quantities; standard deviations "sufficiently smaller" than a and µ_s, making negative values negligible (p. 9) → strategies take arbitrary real values and the remark is not encoded; reason: the affine strategies of Lemma 2 are negative with positive probability under Gaussian signals, so a nonnegativity constraint would contradict Lemma 2, and the remark has no formal content
--   - reading: ε_A and ε_B are independent of ε_a and ε_s and correlated with coefficient η (p. 9) → the pair (ε_A, ε_B) is bivariate normal and independent of the pair (ε_a, ε_s), all four jointly Gaussian; reason: the sentence leaves the joint law open, and E[f_j | f_i] in Lemma 1 requires joint normality; this is the reading under which the paper's formulas hold
--   - encoding: jointly distributed normal noises on an unnamed probability space → the product of four standard normals on ℝ⁴, with the noises as explicit linear forms in the coordinates; reason: this realizes exactly the stated joint law, and every quantity in the statement depends only on that law
--   - encoding: θ, the ratio of two standard deviations → θ ranges over (0, ∞) with σ_a and every other parameter held fixed, and σ_s = θσ_a; reason: this is the comparative static of the proposition; λ_i, β, κ and the thresholds do not depend on θ
--   - encoding: Π^k_i, the ex ante profit at the unique equilibrium, each firm solving max E[π_i | f_i] → the ex ante integral at any ex ante Bayesian Nash equilibrium among measurable square-integrable strategies, compared between any equilibrium at θ1 and any at θ2, together with an existence clause for each θ > 0; reason: Lemma 2 makes the equilibrium unique up to null sets, so no equilibrium has to be chosen, and the existence clause prevents vacuity
-- source:
--   Xing–Liu–Zhang–Zhao, SSRN 4717149 (2023-12-27), Proposition 1 and eq. (9), p. 15; version of record: Management Science (2024), doi:10.1287/mnsc.2023.00304

import Mathlib
import Definitions.Def_CommodityCPC_Model

namespace CommodityCPC

/-- **Proposition 1: equilibrium profits fall and then rise in the price volatility**,
Xing–Liu–Zhang–Zhao, *The Bright Side of Price Volatility in Global Commodity Procurement*, SSRN
4717149 (2023-12-27), Management Science (2024), doi:10.1287/mnsc.2023.00304, Proposition 1 and
eq. (9), p. 15. Let `ρ > 0`, and hold every parameter except `θ` fixed.

* An equilibrium of the CC and of the FC subgame exists at every `θ > 0`.
* (a) In the CC subgame, for a firm `i` with rival `j`, comparing any equilibrium at `θ1` with any
  equilibrium at `θ2`, `0 < θ1 < θ2`: if `1/ρ ≤ θ1` then `Π_i` is weakly higher at `θ2`, and
  strictly higher when `γλ_j(1 + β) ≠ 2`; if `θ2 ≤ 1/ρ` then `Π_i` is weakly lower at `θ2`, and
  strictly lower when `γλ_j(1 + β) ≠ 2`.
* (b) In the FC subgame with `γ ≠ 0`, `Π_A` is strictly higher at `θ2` if `θ^T_A ≤ θ1` and strictly
  lower if `θ2 ≤ θ^T_A`, and likewise for `Π_B` and `θ^T_B`.

**Formalization Note.** `Π^k_i` is the ex ante profit at an equilibrium. Rather than choose one,
the statement compares any two, and the first clause keeps the comparisons from being vacuous.
The strict claims of (a) carry the hypothesis `γλ_j(1 + β) ≠ 2`, because at equality `Π^CC_i` is
constant in `θ`. The thresholds of (9) divide by `ργλ_B(1 + β) > 0` in (b) and by `2ρ > 0`; they
do not depend on `θ`. -/
theorem proposition_1 (p : Params) (hρ : 0 < p.ρ) :
    (∀ θ : ℝ, 0 < θ → (∃ σ, (p.game θ CC).IsBNE σ) ∧ ∃ σ, (p.game θ FC).IsBNE σ) ∧
    (∀ (i : Firm) (θ1 θ2 : ℝ) (σ1 σ2 : Firm → ℝ → ℝ), 0 < θ1 → θ1 < θ2 →
      (p.game θ1 CC).IsBNE σ1 → (p.game θ2 CC).IsBNE σ2 →
      (1 / p.ρ ≤ θ1 →
        p.exAnteProfit θ1 CC i σ1 ≤ p.exAnteProfit θ2 CC i σ2 ∧
        (p.γ * p.lam i.other * (1 + p.β) ≠ 2 →
          p.exAnteProfit θ1 CC i σ1 < p.exAnteProfit θ2 CC i σ2)) ∧
      (θ2 ≤ 1 / p.ρ →
        p.exAnteProfit θ2 CC i σ2 ≤ p.exAnteProfit θ1 CC i σ1 ∧
        (p.γ * p.lam i.other * (1 + p.β) ≠ 2 →
          p.exAnteProfit θ2 CC i σ2 < p.exAnteProfit θ1 CC i σ1))) ∧
    (p.γ ≠ 0 → ∀ (θ1 θ2 : ℝ) (σ1 σ2 : Firm → ℝ → ℝ), 0 < θ1 → θ1 < θ2 →
      (p.game θ1 FC).IsBNE σ1 → (p.game θ2 FC).IsBNE σ2 →
      (p.θTA ≤ θ1 → p.exAnteProfit θ1 FC .A σ1 < p.exAnteProfit θ2 FC .A σ2) ∧
      (θ2 ≤ p.θTA → p.exAnteProfit θ2 FC .A σ2 < p.exAnteProfit θ1 FC .A σ1) ∧
      (p.θTB ≤ θ1 → p.exAnteProfit θ1 FC .B σ1 < p.exAnteProfit θ2 FC .B σ2) ∧
      (θ2 ≤ p.θTB → p.exAnteProfit θ2 FC .B σ2 < p.exAnteProfit θ1 FC .B σ1)) := by sorry

end CommodityCPC
