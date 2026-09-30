-- Prove2me | Theorems.Thm_BayesRouting_Adoption_bwe_iff_optimal
-- name    : BayesRouting.Adoption.bwe_iff_optimal
-- status  : Open
-- author  : @mikedeng1
-- created : 2026-09-29T15:20:29.783564+00:00
-- url     : https://prove2.me/theorems/e0df4500-1482-4af1-a0cd-0103596a6beb
-- title:
--   Theorem 1 — BWE are exactly the minimizers of the weighted potential; the equilibrium edge load is unique
-- statement:
--   Let $\Gamma(\lambda)$ be the Bayesian routing game (standing assumptions as in the game definition, including positive probability of every type profile), and let $\lambda$ satisfy $\lambda^i\ge0$, $\sum_i\lambda^i=1$.
--
--   1. A strategy profile $q$ is a Bayesian Wardrop equilibrium of $\Gamma(\lambda)$ if and only if it is an optimal solution of
--   $$\min\ \Phi(q)\quad\text{s.t.}\quad q\in\mathcal Q(\lambda).\tag{OPT-$\mathcal Q$}$$
--   2. Any two Bayesian Wardrop equilibria of $\Gamma(\lambda)$ induce the same edge load $w^*(\lambda)=(w_e(t))_{e,t}$.
--
--   This characterization is the basis of the whole analysis: it turns equilibrium questions into questions about a convex program and its optimal value $\Psi(\lambda)$, and the uniqueness of the load makes the equilibrium population costs independent of the equilibrium chosen.
--
--   **Formalization Note** The uniqueness claim uses the added assumption that every type profile has positive probability.
-- source:
--   Wu, Amin, Ozdaglar, Value of Information in Bayesian Routing Games, Oper. Res. 69(1) 2021, p. 154, Theorem 1

import Mathlib
import Definitions.Def_BayesRouting_Adoption_Game
import Definitions.Def_BayesRouting_Adoption_Potential

open Finset

namespace BayesRouting.Adoption

/-- Theorem 1 (p. 154). For `λ` in the simplex, a strategy profile is a BWE of `Γ(λ)` if and only
if it minimizes the weighted potential `Φ` over the feasible set `𝒬(λ)` (problem (OPT-𝒬)); and
any two BWE of `Γ(λ)` induce the same edge load `w*(λ)`. -/
theorem bwe_iff_optimal {I : Type} [Fintype I] [DecidableEq I] {T : I → Type} [∀ i, Fintype (T i)]
    [∀ i, DecidableEq (T i)] [∀ i, Nonempty (T i)] {S E R : Type} [Fintype S] [Fintype E]
    [DecidableEq E] [Fintype R] [Nonempty R]
    (G : Game I T S E R) (lam : I → ℝ) (hlam : lam ∈ stdSimplex ℝ I) :
    (∀ q, IsBWE G lam q ↔
      (q ∈ feasibleStrategies G lam ∧
        ∀ q' ∈ feasibleStrategies G lam, potential G q ≤ potential G q')) ∧
    (∀ q q', IsBWE G lam q → IsBWE G lam q' → edgeLoad G q = edgeLoad G q') := by sorry

end BayesRouting.Adoption
