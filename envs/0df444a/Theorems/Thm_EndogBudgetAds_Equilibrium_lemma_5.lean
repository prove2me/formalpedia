-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_5
-- name    : EndogBudgetAds.Equilibrium.lemma_5
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:41.358926+00:00
-- url     : https://prove2.me/theorems/d5f9d1ae-c7e1-4e63-b9ab-6a1503ecc95d
-- title:
--   Lemma 5, p. 28 — E[π̃_j(σ_j, σ*_{−j})] ≤ E[π̃_j(σ*)](1 + 3ϑ/m^{3ϑ/2})
-- statement:
--   There is a universal constant $C > 0$ with the following property. Under the standing assumptions, for every allocation rule, let
--   $$m \ge \max\{(2\vartheta)^\vartheta, \exp(3\vartheta+1)\}, \qquad n \ge 6\vartheta m^{2(\vartheta+1/\vartheta)} \log(m)/C.$$
--   Then for every bidder $j$ and every admissible deviation $\sigma_j$,
--   $$\mathbb E\big[\tilde\pi_j(\sigma_j, \sigma^*_{-j})\big] \le \mathbb E\big[\tilde\pi_j(\sigma^*)\big]\Big(1 + \frac{3\vartheta}{m^{3\vartheta/2}}\Big).$$
--
--   In expectation, σ* is an approximate best response in terms of modified profit; Theorem 1 then accounts for the cost of the unspent budget.
--
--   **Formalization Note** $C$ is universal (quantified first); $m^{3\vartheta/2}$ is `Real.rpow`.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 28, Lemma 5

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 5, p. 28: there is a universal constant `C > 0` such that, for
`m ≥ max{(2ϑ)^ϑ, exp(3ϑ+1)}` and `n ≥ 6ϑ m^{2(ϑ+1/ϑ)} log(m)/C`, every deviation `σ_j` of every bidder
`j` satisfies `E[π̃_j(σ_j, σ*_{−j})] ≤ E[π̃_j(σ*)] (1 + 3ϑ/m^{3ϑ/2})`. -/
theorem lemma_5 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Market, M.Standing →
      ∀ alloc : AllocRule M, IsAllocRule M alloc →
      (2 * vt M) ^ vt M ≤ (M.m : ℝ) →
      Real.exp (3 * vt M + 1) ≤ (M.m : ℝ) →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C ≤ (M.n : ℝ) →
      ∀ (j : Fin M.m) (σj : Strategy M.n), σj.Admissible →
        ∫ V, modProfit M alloc (deviate (sigmaStar M) j σj) j V ∂ valLaw M ≤
          (∫ V, modProfit M alloc (sigmaStar M) j V ∂ valLaw M) *
            (1 + 3 * vt M / (M.m : ℝ) ^ (3 * vt M / 2)) := by sorry

end EndogBudgetAds.Equilibrium
