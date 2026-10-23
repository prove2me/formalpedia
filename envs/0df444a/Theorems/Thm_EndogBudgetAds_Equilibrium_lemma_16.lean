-- Prove2me | Theorems.Thm_EndogBudgetAds_Equilibrium_lemma_16
-- name    : EndogBudgetAds.Equilibrium.lemma_16
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-22T12:33:41.411204+00:00
-- url     : https://prove2.me/theorems/bea69725-7239-4c3d-8f46-363c46211457
-- title:
--   Lemma 16, p. 53 — E[Ψ_j(σ*)] ≥ E[Ψ̄_j](1 − 1/m^{1/ϑ})
-- statement:
--   There is a universal constant $C > 0$ with the following property. Under the standing assumptions, for every allocation rule, let
--   $$m \ge \max\{(2\vartheta)^\vartheta, \exp(3\vartheta+1)\}, \qquad n \ge 6\vartheta m^{2(\vartheta+1/\vartheta)} \log(m)/C.$$
--   Then for every bidder $j$,
--   $$\mathbb E[\Psi_j(\sigma^*)] \ge \mathbb E[\bar\Psi_j]\Big(1 - \frac{1}{m^{1/\vartheta}}\Big).$$
--
--   The realized equilibrium spend nearly exhausts the unbudgeted spend $\bar\Psi_j$, so the unspent part of the budget $B^*_j$ is small relative to $\mathbb E[\bar\Psi_j]$.
--
--   **Formalization Note** $C$ is universal (quantified first); $m^{1/\vartheta}$ is `Real.rpow`.
-- source:
--   Ciocan & Iyer, SSRN 3240995, p. 53, Lemma 16

import Mathlib
import Definitions.Def_EndogBudgetAds_Equilibrium_Model
open MeasureTheory

namespace EndogBudgetAds.Equilibrium

/-- Lemma 16, p. 53: there is a universal constant `C > 0` such that, for
`m ≥ max{(2ϑ)^ϑ, exp(3ϑ+1)}` and `n ≥ 6ϑ m^{2(ϑ+1/ϑ)} log(m)/C`, every bidder's expected spend under
σ* satisfies `E[Ψ_j(σ*)] ≥ E[Ψ̄_j] (1 − 1/m^{1/ϑ})`. -/
theorem lemma_16 :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Market, M.Standing →
      ∀ alloc : AllocRule M, IsAllocRule M alloc →
      (2 * vt M) ^ vt M ≤ (M.m : ℝ) →
      Real.exp (3 * vt M + 1) ≤ (M.m : ℝ) →
      6 * vt M * (M.m : ℝ) ^ (2 * (vt M + 1 / vt M)) * Real.log M.m / C ≤ (M.n : ℝ) →
      ∀ j : Fin M.m,
        (∫ V, PsiBar M j V ∂ valLaw M) * (1 - 1 / (M.m : ℝ) ^ (1 / vt M)) ≤
          ∫ V, spend M alloc (sigmaStar M) j V ∂ valLaw M := by sorry

end EndogBudgetAds.Equilibrium
