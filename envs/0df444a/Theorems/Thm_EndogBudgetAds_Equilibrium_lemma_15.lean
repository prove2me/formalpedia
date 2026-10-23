-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_15
-- name    : EndogBudgetAds.Equilibrium.lemma_15
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:34:35.949415+00:00
-- url     : https://prove2.me/theorems/8c385a0e-f799-4cb1-a7d4-3e90615ee683
-- title:
--   Lemma 15, p. 52 — E[π̃_j(σ_j, σ*_{−j})(1 − 1{E_j(σ_j)})] ≤ (3ϑ/m^{3ϑ/2}) E[π̃_j(σ*)]
-- statement:
--   There is a universal constant $C > 0$ with the following property. Under the standing assumptions, for every allocation rule, let
--   $$m \ge \max\{(2\vartheta)^\vartheta, \exp(3\vartheta+1)\}, \qquad n \ge 6\vartheta m^{2(\vartheta+1/\vartheta)} \log(m)/C.$$
--   Then for every bidder $j$ and every admissible deviation $\sigma_j$,
--   $$\mathbb E\Big[\tilde\pi_j(\sigma_j, \sigma^*_{-j})\,\big(1 - \mathbf 1\{E_j(\sigma_j)\}\big)\Big] \le \frac{3\vartheta}{m^{3\vartheta/2}}\,\mathbb E[\tilde\pi_j(\sigma^*)].$$
--
--   Off the typical event, a deviation can only gain a vanishing fraction of the equilibrium modified profit.
--
--   **Formalization Note** The paper writes $\tilde\pi$ without the index; it is bidder $j$'s modified profit. $\tilde\pi_j(1 - \mathbf 1\{E_j\})$ is the indicator of the complement of $E_j(\sigma_j)$ applied to $\tilde\pi_j$. $C$ is universal (quantified first).
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 52, Lemma 15

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
import Definitions.Def_EndogBudgetAds_Equilibrium_Proof
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 15, p. 52: there is a universal constant `C > 0` such that, for
`m ≥ max{(2ϑ)^ϑ, exp(3ϑ+1)}` and `n ≥ 6ϑ m^{2(ϑ+1/ϑ)} log(m)/C`, every deviation `σ_j` of bidder `j`
satisfies `E[π̃_j(σ_j, σ*_{−j}) (1 − 1{E_j(σ_j)})] ≤ (3ϑ/m^{3ϑ/2}) E[π̃_j(σ*)]`. -/
theorem lemma_15 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Market, M.Standing →
      ∀ alloc : AllocRule M, IsAllocRule M alloc →
      (2 * vt M) ^ vt M ≤ (M.m : ℝ) →
      Real.exp (3 * vt M + 1) ≤ (M.m : ℝ) →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C ≤ (M.n : ℝ) →
      ∀ (j : Fin M.m) (σj : Strategy M.n), σj.Admissible →
        ∫ V, (EventJ M j σj)ᶜ.indicator
            (fun V => modProfit M alloc (deviate (sigmaStar M) j σj) j V) V ∂ valLaw M ≤
          3 * vt M / (M.m : ℝ) ^ (3 * vt M / 2) *
            ∫ V, modProfit M alloc (sigmaStar M) j V ∂ valLaw M := by sorry

end EndogBudgetAds.Equilibrium
