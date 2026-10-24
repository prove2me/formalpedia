-- Prove2me | Theorems.Thm_ContextualAuctions_Existence_proposition_1
-- name    : ContextualAuctions.Existence.proposition_1
-- status  : Proved
-- author  : @mikedeng1
-- created : 2026-10-15T19:28:57.966243+00:00
-- url     : https://prove2.me/theorems/c67baa4f-a43c-45c6-b646-4e629b1d4bd0
-- title:
--   Proposition 1, p. 8 — strong duality: for a.e. type, a dual minimizer t* makes σ^µ_α(wᵀα/(1+t*)) optimal for Q^µ(w,B)
-- statement:
--   Work in the contextual first price auction model with budgets (see the `Setting` module), under its standing assumptions. There is a set $\Theta'\subset\Theta$ with $G(\Theta')=1$ such that the following holds for **every** pacing function $\mu$ and every type $(w,B)\in\Theta'$: if
--
--   $$
--   t^*\in\arg\min_{t\ge0}q^\mu(w,B,t),
--   $$
--
--   then the bid function $\alpha\mapsto\sigma^\mu_\alpha\big(w^T\alpha/(1+t^*)\big)$ is an optimal solution of the budget-constrained problem $Q^\mu(w,B)$: it is admissible, its expected payment is at most $B$, and no admissible bid function with expected payment at most $B$ earns a higher expected utility against competitors using $\beta^\mu$.
--
--   The buyer's problem is not convex, so this strong duality is not a consequence of convex duality. It reduces the search for an equilibrium to the choice of one scalar $\mu(w,B)$ per type.
--
--   **Formalization Note** The set $\Theta'$ is chosen before $\mu$: one set serves all pacing functions. It is required to be Borel measurable, which loses nothing since every Lebesgue measurable set of full measure contains a Borel one. The paper prints the argmin as "$\arg\min_{t^*\ge0}$"; the bound variable is $t$. Membership in the argmin is written as $t^*\ge0$ together with minimality over $[0,\infty)$. Pacing functions are measurable.
-- source:
--   Balseiro, Kroer, Kumar, Contextual Standard Auctions with Budgets: Revenue Equivalence and Efficiency Guarantees, Management Science, Articles in Advance (2023), doi:10.1287/mnsc.2023.4719, p. 8, Proposition 1

import Mathlib
import Definitions.Def_ContextualAuctions_Existence_Setting

namespace ContextualAuctions.Existence

theorem proposition_1 (M : Model) (hM : M.Standing) :
    ∃ Θ' ⊆ Theta M, MeasurableSet Θ' ∧ M.G Θ' = 1 ∧
      ∀ μ : (Fin M.d → ℝ) × ℝ → ℝ, IsPacing M μ → ∀ θ ∈ Θ', ∀ tstar : ℝ, 0 ≤ tstar →
        IsMinOn (qDual M μ θ) (Set.Ici 0) tstar →
          IsOptimal M (beta M μ) θ (fun α => sigma M μ α (val θ α / (1 + tstar))) := by sorry

end ContextualAuctions.Existence
