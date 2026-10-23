-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_17
-- name    : EndogBudgetAds.Equilibrium.lemma_17
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:59.304422+00:00
-- url     : https://prove2.me/theorems/3e43b5ee-6725-4988-9dc9-c46da2aa1303
-- title:
--   Lemma 17, p. 54 — E[π̃_j(σ*)] ≥ (9(1+r_j)/(10θmax)) Σ_i P(i ∈ U^W_{j,1}) ≥ (9(1+r_j)/(10ϑ log m)) E[Ψ̄_j]
-- statement:
--   There is a universal constant $C > 0$ with the following property. Under the standing assumptions, for every allocation rule, let
--   $$m \ge \max\{(2\vartheta)^\vartheta, \exp(3\vartheta+1)\}, \qquad n \ge 6\vartheta m^{2(\vartheta+1/\vartheta)} \log(m)/C.$$
--   Then for every bidder $j$,
--   $$\mathbb E[\tilde\pi_j(\sigma^*)] \ge \frac{9(1+r_j)}{10\theta_{\max}} \sum_i \mathbb P\big(i \in U^W_{j,1}\big) \ge \frac{9(1+r_j)}{10\vartheta\log m}\,\mathbb E[\bar\Psi_j].$$
--
--   The equilibrium modified profit is of the same order as the unbudgeted spend divided by $\vartheta \log m$, which is what lets the slack cost of the budgets be absorbed in Theorem 1.
--
--   **Formalization Note** $C$ comes before the market (universal). $\log$ is natural; $m^{x}$ is `Real.rpow`.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 54, Lemma 17

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 17, p. 54: there is a universal constant `C > 0` such that, for
`m ≥ max{(2ϑ)^ϑ, exp(3ϑ+1)}` and `n ≥ 6ϑ m^{2(ϑ+1/ϑ)} log(m)/C`, every bidder's expected modified
profit under σ* satisfies
`E[π̃_j(σ*)] ≥ (9(1+r_j)/(10θmax)) Σ_i P(i ∈ U^W_{j,1}) ≥ (9(1+r_j)/(10ϑ log m)) E[Ψ̄_j]`. -/
theorem lemma_17 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Market, M.Standing →
      ∀ alloc : AllocRule M, IsAllocRule M alloc →
      (2 * vt M) ^ vt M ≤ (M.m : ℝ) →
      Real.exp (3 * vt M + 1) ≤ (M.m : ℝ) →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C ≤ (M.n : ℝ) →
      ∀ j : Fin M.m,
        9 * (1 + M.r j) / (10 * M.θmax) *
            ∑ i, (valLaw M).real {V | IsTop (fun l => W M V l i) j} ≤
          ∫ V, modProfit M alloc (sigmaStar M) j V ∂ valLaw M ∧
        9 * (1 + M.r j) / (10 * vt M * Real.log M.m) * ∫ V, PsiBar M j V ∂ valLaw M ≤
          9 * (1 + M.r j) / (10 * M.θmax) *
            ∑ i, (valLaw M).real {V | IsTop (fun l => W M V l i) j} := by sorry

end EndogBudgetAds.Equilibrium
