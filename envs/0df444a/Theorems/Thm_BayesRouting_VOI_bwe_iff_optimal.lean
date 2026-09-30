-- Prove2me | Theorems.Thm_BayesRouting_VOI_bwe_iff_optimal
-- name    : BayesRouting.VOI.bwe_iff_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T14:54:05.922423+00:00
-- url     : https://prove2.me/theorems/c7028e06-4ec9-4acf-b31f-2028b44484db
-- title:
--   Theorem 1 — BWE are exactly the minimizers of $\Phi$ over $\mathcal Q(\lambda)$; the equilibrium edge load is unique
-- statement:
--   Let $\lambda$ be a size vector ($\lambda^i\ge0$, $\sum_i\lambda^i=1$). A strategy profile $q$ is a Bayesian Wardrop equilibrium of $\Gamma(\lambda)$ if and only if it is an optimal solution of the convex program
--
--   $$\min\ \Phi(q)\quad\text{s.t.}\quad q\in\mathcal Q(\lambda).\qquad(\text{OPT-}\mathcal Q)$$
--
--   Moreover, all BWE of $\Gamma(\lambda)$ induce the same edge load: if $q,q'$ are BWE then $w_e(t)$ computed from $q$ equals $w_e(t)$ computed from $q'$ for every edge $e$ and type profile $t$. This is the equilibrium edge load $w^*(\lambda)$.
--
--   Because equilibrium costs depend on $q$ only through the edge load, the uniqueness of $w^*(\lambda)$ makes the equilibrium population costs $C^{i*}(\lambda)$ independent of the chosen BWE.
--
--   **Formalization Note** Uniqueness of the edge load relies on the added full-support assumption on the prior.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 154, Theorem 1

import Mathlib
import Definitions.Def_BayesRouting_VOI_Game
import Definitions.Def_BayesRouting_VOI_Potential

namespace BayesRouting.VOI

/-- **Theorem 1** (Wu, Amin, Ozdaglar, Oper. Res. 69(1) 2021, p. 154). For a size vector `λ` in
the simplex, a strategy profile is a BWE of `Γ(λ)` if and only if it minimizes `Φ` over `𝒬(λ)`
(OPT-𝒬); and all BWE induce the same edge load `w^*(λ)`. -/
theorem bwe_iff_optimal {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I) :
    (∀ q : (i : I) → T i → R → ℝ, IsBWE G lam q ↔
        (q ∈ feasibleStrategies G lam ∧
          ∀ q' ∈ feasibleStrategies G lam, potential G q ≤ potential G q')) ∧
      ∀ q q' : (i : I) → T i → R → ℝ, IsBWE G lam q → IsBWE G lam q' →
        edgeLoad G q = edgeLoad G q' := by sorry

end BayesRouting.VOI
