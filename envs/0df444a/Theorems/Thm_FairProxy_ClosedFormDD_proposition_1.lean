-- Prove2me | Theorems.Thm_FairProxy_ClosedFormDD_proposition_1
-- name    : FairProxy.ClosedFormDD.proposition_1
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-10-19T01:23:18.098665+00:00
-- url     : https://prove2.me/theorems/3bff10b9-23cb-4fe6-8242-c1ba55ffe27e
-- title:
--   Proposition 1, p. 10 — Fréchet–Hoeffding bounds for finite couplings
-- statement:
--   Let $\sigma$ and $\tau$ be nonnegative probability vectors on finite sets $\mathcal S$ and $\mathcal T$. A matrix $\pi$ is their coupling exactly when it has the prescribed row and column sums and satisfies the entrywise Fréchet–Hoeffding bounds:
--
--   $$
--   \max\{\sigma(s)+\tau(t)-1,0\}\le\pi(s,t)\le\min\{\sigma(s),\tau(t)\}
--   \qquad(s\in\mathcal S,t\in\mathcal T).
--   $$
--
--   This characterizes the possible class–outcome joint probabilities from their two marginals.
-- source:
--   Kallus, Mao & Zhou, Assessing Algorithmic Fairness with Unobserved Protected Class Using Data Combination, arXiv:1906.00285v2, p. 10, Proposition 1, Eq. (2)

import Mathlib
import Definitions.Def_FairProxy_ClosedFormDD_Coupling

namespace FairProxy.ClosedFormDD

/-- Proposition 1, p. 10, equation (2): the entrywise Fréchet–Hoeffding characterization. -/
theorem proposition_1 {S T : Type*} [Fintype S] [Fintype T]
    (σ : S → ℝ) (τ : T → ℝ)
    (hσ_nonneg : ∀ s, 0 ≤ σ s) (hτ_nonneg : ∀ t, 0 ≤ τ t)
    (hσ_sum : ∑ s, σ s = 1) (hτ_sum : ∑ t, τ t = 1) :
    couplingSet σ τ =
      {π | (∀ s, ∑ t, π s t = σ s) ∧
           (∀ t, ∑ s, π s t = τ t) ∧
           ∀ s t, max (σ s + τ t - 1) 0 ≤ π s t ∧
             π s t ≤ min (σ s) (τ t)} := by sorry

end FairProxy.ClosedFormDD
